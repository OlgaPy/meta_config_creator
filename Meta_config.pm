package Dlink;
require Exporter;
use Data::Dumper;
use List::Util qw(min max);
use Translator;
use strict;
use Switch;
use Socket;
use Net::hostent;

use JSON;
#S---------------------
use Crypt::RC4;

use MIME::Base64;

use Digest::MD5 qw(md5_hex);

use Encode;
#E--------------------

our @ISA = qw(Exporter);
our %EXPORT_TAGS = ( 'all' => [ qw(QOS LoopDetect Filter SYSLOG STP VLAN ManagementACL SNMP MacNotification StormControl TrafficSegmentation ConfigPort isValidPort Radius NTP Jumbo IPTV) ] );
our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );
our @EXPORT = qw( );

#our $PORTREGEXP = '1\/(\d+)';
#our $PORTS = '[\d,-:]+';
#our $PORTREGEXP = '^(\d+)$|^1\/(\d+)$';
our $LAG = undef;
our $PORTS = '[\d,-:()]+';

our $eqm_delimiter = '';
our $eqm_modules = 0; #boolean, 1 if exists module number >1
our $eqm_module_name = '1';

our $SECTIONCONFIG = undef;

sub ConfigPort {
    my $mod = shift;
    my $input_hashref = shift;
    undef $LAG;
    $eqm_delimiter = '';
    $eqm_modules = 0;
    $eqm_module_name = '1';
    foreach my $eqm_number (keys %{$input_hashref->{port}}){
        if ($eqm_number =~ /\d+:\d+/) {
            $eqm_delimiter = ':';
        } elsif ($eqm_number =~ /\d+\/\d+/){
            $eqm_delimiter = '/';
        }
        $eqm_number =~ m/([0-9A-Za-z]+)[:\/](\d+)/;
        my $tmp = $1;
        if (defined $tmp && $tmp > 1)  {
            $eqm_modules = 1;
        }
        if ($tmp =~ /Slot/) {
            $eqm_module_name = $tmp;
        }
    }
}

sub isValidPort {
    my $mod = shift;
    my $portstring = shift;
    my $PORTREGEXP = '^(\d+)$|^\d+[\/:](\d+)$|^Slot\d+[\/:](\d+)$';
    if ($portstring =~ m/$PORTREGEXP/){
        return 1;
    } else {
        return 0
    }
}

sub QOS {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;
    my $configstr = join "\n", @$configref;
    my $model = Translator::GetModel();

    my @QOS_LABELS = (0..7);
    my @QOS_QUEUES = (0..7);
    my @VOIP_MAC = (
        '00-90-8F-00-00-00',
        '00-0E-08-00-00-00',
        '00-02-A4-00-00-00',
        'C4-0A-CB-00-00-00',
        'C4-64-13-00-00-00',
        '30-E4-DB-00-00-00',
        '88-75-56-00-00-00',
        '64-9E-F3-00-00-00',
        '54-78-1A-00-00-00'
    );

    #Список очередей на всем обрудовании приводим к стандартному списку очередей(4 очереди, начиная с 0), Порядковый номер очереди зависит от приоритета очереди (веса). очередь "3" - самая приор
    #
    #
    #  <qos>
    #       <default>$queu</default>
    #       <1><>
    #  </qos>

    # ${$hashref}->{'model'} = $model;

    my $userpriority = {};
    my $queue_weight = {};
    my $queue_priority = {};  #param_queue => real_queue

    foreach my $port (keys %{${$hashref}->{'port'}}) {
        ${$hashref}->{port}->{$port}->{'trust_cos'} = 'disable';
    }

    #транслируем имена очередей к стандартному списку приоритетов очередей.
    #Сначала определяем распределение меток по очередям, при этом убедившись, что включен 802.1p
    foreach (grep {/config\s+cos\s+mapping\s+port\s+[\d,-]+\s+ethernet\s+802\.1p/} @str){
        $_=~ m/config\s+cos\s+mapping\s+port\s+($PORTS)\s+ethernet\s+802\.1p/;
        my $port_str = $1;
        foreach my $port (ParsePorts ($port_str)){
            ${$hashref}->{port}->{$port}->{'qos_mapping'}->{'type'} = '802.1p';
            ${$hashref}->{port}->{$port}->{'trust_cos'} = 'enable';
        }
    }

    ### DDS-10965 ###

    if ( $configstr =~ /config\s+cos\s+mapping\s+port\s+($PORTS)\s+none\s*config\s+cos\s+mapping\s+port\s+($PORTS)\s+802\.1p/ ){
        foreach my $port (ParsePorts ($2)) {
            ${$hashref}->{port}->{$port}->{'trust_cos'} = 'enable';
        }
        if ( $configstr =~ /config\s+cos\s+mapping\s+port\s+($PORTS)\s+dscp/ ){
            foreach my $port (ParsePorts ($1)) {
                ${$hashref}->{port}->{$port}->{'trust_cos'} = 'enable, remove dscp';
            }
        }
    }

    if ($model =~ m/DES-(3200-(\d+(\/ME|F)?\/C|52)|3526)/ or $model =~ m/DES-3200-28P Fast/){
        if (not grep {/config\s+cos\s+mapping\s+port\s+[\d,-]+\s+ethernet\s+802\.1p/} @str ){
            foreach my $port (keys %{${$hashref}->{'port'}}) {
                ${$hashref}->{port}->{$port}->{'trust_cos'} = 'enable';
            }
        }
    }

    if ($model =~ m/DGS-3(1|4|6)20-2(4|6|8)SC/ or $model =~ m/DGS-3000-\d+TC/ or $model =~ /D-link Stack/){
        if (not grep {/config\s+dscp\s+trust\s+($PORTS)\s+state\s+enable/} @str ){
            foreach my $port (keys %{${$hashref}->{'port'}}) {
                ${$hashref}->{port}->{$port}->{'trust_cos'} = 'enable';
            }
        }
        else{
            foreach my $port (keys %{${$hashref}->{'port'}}) {
                ${$hashref}->{port}->{$port}->{'trust_cos'} = 'remove dscp trust';
            }
        }
    }

    ${$hashref}->{'hol_prevention'} = 'disable';
    if (my @grep = grep {/(enable|disable)\s+hol_prevention/} @str ){
        $grep[0] =~ /(enable|disable)\s+hol_prevention/;
        ${$hashref}->{'hol_prevention'} = $1;
    }

    #################

    foreach my $port (keys %{${$hashref}->{'port'}}) {
        foreach (@QOS_LABELS){
            ${$hashref}->{'port'}->{$port}->{'qos_mapping'}->{'label'}->{$_}='';
        }
    }

    foreach my $grep (grep {/config\s+802\.1p\s+user_priority/} @str){
        $grep =~ m/config\s+802\.1p\s+user_priority\s+(?:ports\s+\S+\s+)?(\d+)\s+(\d+)/;
        my $usr_p = $1;
        my $queue = $2;
        foreach my $port (keys %{${$hashref}->{'port'}}) {
            ${$hashref}->{port}->{$port}->{'qos_mapping'}->{'label'}->{$usr_p} = $queue;
        }
    }

    foreach (@QOS_QUEUES) {
        ${$hashref}->{'qos'}->{'weights'}->{$_} = '';
    }

    my @stricts;
    my @eights;
    foreach my $grep (grep {/config\s+scheduling\s+/} @str){
        my $queue;
        my $weight;
        if ($grep =~ /config\s+scheduling\s+(?:ports\s+\S+\s+)?(\d+)\s+weight\s+(\d+)/){
            $queue = $1;
            $weight = $2;
            push @eights, $queue if $weight eq 8;
            ${$hashref}->{'qos'}->{'weights'}->{$queue} = $weight;
        }
        if ($grep =~ /config\s+scheduling\s+(?:ports\s+\S+\s+)?(\d+)\s+strict/) {
            $queue = $1;
            $weight = 'strict';
            push @stricts, $queue;
        }
    }

    ### DDS-10965 ###

    ${$hashref}->{'qos'}->{'mechanism'} = 'none';
    if (my @grep = grep {/config\s+scheduling_mechanism\s+(?:ports\s+\S*\s+)?(\S+)$/} @str){
        $grep[0] =~ /config\s+scheduling_mechanism\s+(?:ports\s+\S*\s+)?(\S+)$/;
        ${$hashref}->{'qos'}->{'mechanism'} = $1;
    }

    if ($model =~ m/3526/){
        ${$hashref}->{'qos'}->{'mechanism'} = 'strict';
        ${$hashref}->{'qos'}->{'weights'}->{'0'} = '1';
        ${$hashref}->{'qos'}->{'weights'}->{'1'} = '2';
        ${$hashref}->{'qos'}->{'weights'}->{'2'} = '4';
        ${$hashref}->{'qos'}->{'weights'}->{'3'} = '8';
    }

    if ($model =~ 'DES-1210' and ${$hashref}->{'qos'}->{'mechanism'} eq 'strict') {
        ${$hashref}->{'qos'}->{'mechanism'} .= ', should be 1st3wrr';
    }

    if ( ($model =~ m/DGS-3(1|4|6)20-2(4|6|8)SC/ or $model =~ m/DGS-3000-\d+TC/) and ${$hashref}->{'qos'}->{'mechanism'} ne 'wrr' ){
        ${$hashref}->{'qos'}->{'mechanism'} .= ', should be wrr';
    }

    if ( $model =~ m/DES-3200-(\d+(\/ME|F)?\/C|52)/ or $model =~ m/DGS-3120-2(4|6|8)SC/ or $model =~ m/DGS-3000-\d+TC/ or $model =~ m/DES-3200-28P Fast/){
        ${$hashref}->{'qos'}->{'weights'}->{3} = 'should be strict';
    }

    foreach my $queue ( @stricts ){
        ${$hashref}->{'qos'}->{'weights'}->{$queue} = 'strict';
    }

    if ( $model =~ m/(DES-3200-\d+\/A1|DES-1228\/ME\/B1)/ or $model =~ m/DES-3200-2(6$|8F? (Fast|Metro))/){
        if ( not grep {/3/} @eights or not grep {/3/} @stricts ){
            ${$hashref}->{'qos'}->{'weights'}->{3} = 'should be both strict and weight 8';
        }
    }

    #################


    foreach my $port (keys %{${$hashref}->{'port'}}) {
        ${$hashref}->{'port'}->{$port}->{'qos_criteria'}->{'default'} = '';
        foreach (@VOIP_MAC){
            ${$hashref}->{'port'}->{$port}->{'qos_criteria'}->{'mac_prefix'}->{$_}='';
        }
    }

    foreach my $g ( grep {/config\s+802\.1p\s+default_priority/} @str){
        $g=~ m/config\s+802\.1p\s+default_priority\s+($PORTS)\s+(\d+)/;
        my $port_str = $1;
        my $prior = $2;
        foreach my $port (ParsePorts ($port_str)){
            ${$hashref}->{'port'}->{$port}->{'qos_criteria'}->{'default'}= $prior;
        }
    }

    #Теперь QOS для mac-префиксов
    my @filter_str = grep {/.*access_profile.*/} @str;
    my %current_profile_hash;
    foreach my $str (@filter_str){
        if ($str =~ /create\s+access_profile.*profile_id\s+(\d+).*/){
            my $profile_id = $1;
            if ($str =~ /ethernet\s+source_mac\s+[Ff]+-*[Ff]+-*[Ff]+-*00-*00-*00/){
                $current_profile_hash{$profile_id}=$str if (defined $profile_id);  #ex. {10 => 'create access_profile ethernet source_mac FF-FF-FF-00-00-00 ethernet_type profile_id 10'}
            }
        }
    }
    foreach  my $k (keys %current_profile_hash) {
        my @tmp_str = grep {/^config.*profile_id\s+$k\s+.*$/} @filter_str;
        foreach my $config_str (@tmp_str){
            foreach my $f (@VOIP_MAC){
                if ($config_str =~ /source_mac\s+$f\s+(?:mask\s+FF-FF-FF-00-00-00\s+)?(?:ethernet_type\s+0x8864\s+)?port\s+($PORTS)\s+(deny|permit).*priority.*\s+(\d+).*$/){
                    my $port_str = $1;
                    my $prior = $3;
                    if ($2 eq 'permit') {
                        foreach my $port (ParsePorts ($port_str)){
                            my $real_queue = ${$hashref}->{'port'}->{$port}->{'qos_mapping'}->{'label'}->{$prior};
                            ${$hashref}->{'port'}->{$port}->{'qos_criteria'}->{'mac_prefix'}->{$f}= $real_queue;
                        }
                    }
                }
            }
        }
    }
    1;
}

#S---------------------
sub decrypt($$)
{
    my $key = shift;
    my $encrypted = shift;
    return undef if $key !~ /^[\da-f]+$/i;
    return undef if $encrypted !~ /^[\da-z+\/=]+$/i;
    my $decrypt = RC4( pack("H*", $key), decode_base64($encrypted) );
    return $decrypt;
}

sub parse_cfg($\%\@;$)
{

    my $config_file   = shift;
    my $cfg_hash      = shift;
    my $necess_params = shift;
    my $case = shift;
    my $section_name;
    my $var;
    my $value;
    $config_file = $ENV{"EQ_CONF_FILE"} if ! defined $config_file and defined $ENV{"EQ_CONF_FILE"};
    return "Couldn't open config file: file not defined" unless defined $config_file;
    open FH, "<$config_file" or return "Couldn't open config file '$config_file': '$!'";
    while (<FH>)

    {

        ## process coments with symbol '#'
        $_ =~ s/#.*$//;
        ## process section name in configuration file
        if ($_ =~ /^\s*\[(.*)\]\s*$/)
        {
            $section_name = uc $1;
            next;
        }

        ## process section contents

        ##print $section_name."\n";

        if ($section_name !~ /^\s*$/ and $_ !~ /^\s*$/)
        {
            ($var, $value) = split /[=\s]{1,}/, $_, 2;
            $var =~ s/^\s*//;
            $var =~ s/\s*$//;
            $value =~ s/^\s*//;
            $value =~ s/\s*$//;
            if (! defined $case or $case eq 'upper') # by default upper case
            {
                $var = uc $var;
            }
            elsif ($case eq 'lower')
            {
                $var = lc $var;
            }
            else
            {
                ## as is
            }
            if (exists $cfg_hash->{$section_name})
            { $cfg_hash->{$section_name}->{$var} = $value; }
            else
            { $cfg_hash->{$section_name} = {$var => $value}; }
        }
    }

    ## determine necessary parameters in configuration, terminate program if failed
    foreach my $param (@$necess_params)
    {
        unless ( exists $cfg_hash->{$param->[0]}->{$param->[1]} )
        { return "Can't find necessary parameter '$param->[1]' in section [$param->[0]]. Configuration file: '$config_file'"; }
    }
    return undef;

}
#E---------------------------------------------

sub decrypter_eqm($){
    my $value_encrypt = shift;

    my $config_file = '/home/equipment/EQ-scripts/equipment.conf';
    #S-------------------
    my %CFG;
    my @necessary_params = (["SCRIPTS","DECRYPT_KEY"],);
    parse_cfg($config_file,%CFG,@necessary_params);
    my $value_decript =  decrypt($CFG{SCRIPTS}{DECRYPT_KEY}, $value_encrypt);

    return $value_decript;
    # return 1;
}



sub Filter {
    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my $encrypted_ro_community = ${$hashref}->{'common'}->{'encrypted_ro_community'};

    my $decrypted_ro_community = decrypter_eqm( $encrypted_ro_community);

    my $test_net_address = ${$hashref}->{'common'}->{'net_address'};
    # print ($test_net_address. "\n". $test_decrypted_ro_community. "\n");
    # my $out_snmp = `/opt/equipment/EQ-scripts/validation/test_olga/snmp_test.py 10.255.80.4 rjydjq17`;
    # my $out_snmp = `/opt/equipment/EQ-scripts/validation/test_olga/snmp_test.py $test_net_address $test_decrypted_ro_community`;

    my $model_dev = Translator::GetModel();
    # print $model_dev;
    # exit();
    ${$hashref}->{'model'} = $model_dev;

    # print Dumper('/opt/equipment/EQ-scripts/validation/test_olga/snmp_test.py '. $test_net_address . $decrypted_ro_community . $model_dev);
    # exit();
    # print ($test_net_address ."\n". $decrypted_ro_community."\n". $model_dev);
    # exit();
    # print Dumper($test_net_address. "\n" . $decrypted_ro_community. "\n". $model_dev);
    # exit(0);
    my $out_snmp = `/opt/equipment/EQ-scripts/validation/test_olga/snmp_test.py \'$test_net_address\' \'$decrypted_ro_community\' \'$model_dev\'`;


    my $out_json_snmp =decode_json( $out_snmp);


    my @str = @$configref;

    my $default_action = 'permit';
    my %filter_profile_hash = (
        'default' => 'ethernet.*source_mac\s+00-*00-*00-*00-*00-*00',
        'pvst' => 'ethernet.*destination_mac\s+[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+',
        'cdp' => 'ethernet.*destination_mac\s+[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+-*[Ff]+',
        'pppoe_ds' => 'ethernet.*ethernet_type',
        'pppoe_ss' => 'ethernet.*ethernet_type',
        'lbd' => 'ethernet.*ethernet_type',
        'arp' => 'ethernet.*ethernet_type',
        'eapol' => 'ethernet.*ethernet_type',
        'bpdu' => 'ethernet.*destination_mac\s+[Ff]+-*[Ff]-*[Ff]-*[Ff]-*[Ff]-*[Ff]+',
        'dhcp' => 'udp\s+dst_port[_mask]*\s+0x[Ff]+',
        'provisioning' => 'ip\s+source_ip[_mask]*\s+255\.255\.[255]|[250]\.0',
        'ipv6' => 'ethernet.*ethernet_type'
    );

    my %filter_param_hash = (
        'pvst' => 'ethernet\s+destination_mac\s+01-00-0C-CC-CC-CD',
        'cdp' => 'ethernet\s+destination_mac\s+01-00-0C-CC-CC-CC',
        'pppoe_ds' => 'ethernet\s+ethernet_type\s+0x8863',
        'pppoe_ss' => 'ethernet\s+ethernet_type\s+0x8864',
        'lbd' => 'ethernet\s+ethernet_type\s+0x9000',
        'arp' => 'ethernet\s+ethernet_type\s+0x0?806',
        'eapol' => 'ethernet\s+ethernet_type\s+0x888[Ee]',
        'bpdu' => 'ethernet\s+destination_mac\s+01-80-C2-00-00-00',
        'dhcp' => 'ip\s+udp\s+dst_port\s+67',
        'provisioning' => 'ip\s+source_ip',
        'default' => 'ethernet\s+source_mac\s+00-00-00-00-00-00',
        'ipv6' => 'ethernet\s+ethernet_type\s+0x86[Dd][Dd]'
    );


    # my @founds_model_device = grep {/^\#\s+(.*?)\s+Configuration$/} @str;


    # my @descr_ports = grep {/^\s*config\s+.*?ports\s+($PORTS).*?(enable|disable)\s+(\S+)$/} @str;
    my @duplex_ports = grep {/^\s*config\s+.*?ports\s+($PORTS).*?speed\s+(\S+)\s+.*?(enable|disable)(.*?|)$/} @str;
    my %stdict_duplex;
    foreach my $dup (@duplex_ports){
        $dup =~ /^\s*config\s+.*?ports\s+($PORTS).*?speed\s+(\S+)\s+.*?(enable|disable)(.*?|)$/;
        my $port_one = $1;
        my $duplex_one = $2;

        # print  $port_one. "____1\n".$duplex_one. "____2\n". "---------------\n";
        foreach my $port_one_duplex (ParsePorts($port_one)){
            %stdict_duplex -> {$port_one_duplex} -> {'duplex'}= 'null';
            %stdict_duplex -> {$port_one_duplex} -> {'speed_manual'}= 'null';

            if ($duplex_one eq 'auto'){
                %stdict_duplex -> {$port_one_duplex} -> {'duplex'}= 'auto';
                %stdict_duplex -> {$port_one_duplex} -> {'speed_manual'}= 'auto';
            }
            if($duplex_one =~ m/(\d+)\_(\S+)/) {
                %stdict_duplex -> {$port_one_duplex} -> {'duplex'}= $2;
                %stdict_duplex -> {$port_one_duplex} -> {'speed_manual'}= $1;
            }
        }
    }

    # my @model = grep {/^\s*\#\s+(.*?)\s+Configuration\s*$/} @str;
    # ${$hashref}->{DEBUG} = Dumper(@model);
    my %stuff_dict;
    my $desc_one = 'null';
    my @descr_ports = grep {/^\s*config\s+.*?ports\s+($PORTS).*?(enable|disable)\s+(description\s+|)(\S+|clear_description)$/} @str;
    foreach my $desc (@descr_ports){
        # $desc =~/^\s*config\s+.*?ports\s+(25).*?(enable|disable)\s+(\S+)$/;
        $desc =~ /^\s*config\s+.*?ports\s+($PORTS).*?(enable|disable)\s+(description\s+|)(\S+|clear_description)$/;
        # $desc_one = $3;
        $desc_one = $4;
        my $port_one = $1;
        # print $desc_one;
        foreach my $port_one_descr (ParsePorts($port_one)){
            # print "|". $desc. "|\n";
            if ($desc_one eq 'clear_description'){
                %stuff_dict -> {$port_one_descr} = 'null';
            }
            else{
                $desc_one =~ s/'//g;
                $desc_one =~ s/"//g;
                %stuff_dict -> {$port_one_descr} = $desc_one;
            }
        }
    }

    foreach my $port (keys %{${$hashref}->{port}}) {
        foreach my $f (keys %filter_param_hash){
            ${$hashref}->{port}->{$port}->{filter}->{$f} = $default_action;

            ${$hashref}->{port}->{$port} -> {'duplex'} = %stdict_duplex -> {$port} -> {'duplex'};
            ${$hashref}->{port}->{$port} -> {'speed_manual'} = %stdict_duplex -> {$port} -> {'speed_manual'};
            ${$hashref}->{port}->{$port} -> {description} = %stuff_dict -> {$port};
            ${$hashref}->{port}->{$port} -> {'ifOperStatus'} = 'null';
            ${$hashref}->{port}->{$port} -> {'ifAdminStatus'} = 'null';
            ${$hashref}->{port}->{$port} -> {'ifOutOctets'} = 'null';
            ${$hashref}->{port}->{$port} -> {'ifInOctets'} = 'null';
            ${$hashref}->{port}->{$port} -> {'media_type'} = 'null';
            $port =~ m/(\d+)/;
            $port =~ m/(\d+)\/(\d+)/;
            if ( !defined($2) ){
                my $short_port = 0;
            }
            else{
                ${$hashref}->{port}->{$port} -> {'traffic_here'} = 'null';
                my $short_port = $2;
                my $port_ifOperStatus = $out_json_snmp -> {'ifOperStatus'} -> {$short_port};
                ${$hashref}->{port}->{$port} -> {'ifOperStatus'} = $port_ifOperStatus;
                # print ($short_port. $port_ifOperStatus. "\n");
                my $port_ifAdminStatus = $out_json_snmp -> {'ifAdminStatus'} -> {$short_port};
                ${$hashref}->{port}->{$port} -> {'ifAdminStatus'} = $port_ifAdminStatus;
                my $port_ifOutOctets = $out_json_snmp -> {'ifOutOctets'} -> {$short_port};
                ${$hashref}->{port}->{$port} -> {'ifOutOctets'} = $port_ifOutOctets;
                my $port_ifInOctets = $out_json_snmp -> {'ifInOctets'} -> {$short_port};
                ${$hashref}->{port}->{$port} -> {'ifInOctets'} = $port_ifInOctets;
                my $port_media_type= $out_json_snmp -> {'media_type'} -> {$short_port};
                ${$hashref}->{port}->{$port} -> {'media_type'} = $port_media_type;
            }

        }
    }

    my @filter_str = grep {/access_profile/} @str;
    my  %current_profile_hash;
    foreach my $str (@filter_str){
        if ($str =~ /create\s+access_profile.*profile_id\s+(\d+)/){
            $current_profile_hash{$1}=$str if (defined $1);  #ex. {10 => 'create access_profile ethernet source_mac FF-FF-FF-00-00-00 ethernet_type profile_id 10'}
        }
    }
    foreach  my $k (sort {$b<=>$a} keys %current_profile_hash){
        my @tmp_str = grep {/profile_id\s+$k/} @filter_str;
        #Все правила и профили прогоняем в обратном порядке
        foreach my $config_str (reverse @tmp_str){

            foreach my $f (keys %filter_param_hash){
                if ($config_str =~ $filter_param_hash{$f}){
                    if ($current_profile_hash{$k} =~ $filter_profile_hash{$f}){
                        if ($config_str =~ /^.*port\s+($PORTS)\s+(deny|permit)\s*/){

                            my @ports = ParsePorts($1) if (defined $1);
                            my $action = $2 if (defined $2);
                            if (defined $action){
                                #Применяем дефолтное правило на все типы фильтров
                                if ($f eq 'default') {
                                    foreach my $f (keys  %filter_param_hash) {
                                        foreach my $i (@ports){
                                            ${$hashref}->{port}->{$i}->{filter}->{$f} = $action;
                                        }
                                    }
                                }else{
                                    foreach my $i (@ports){
                                        ${$hashref}->{port}->{$i}->{filter}->{$f} = $action;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }







    my @port_seq_array = grep {/^\s*config\s+port_security\s+ports\s+($PORTS)\s+.*state\s+(enable|disable).*/} @str;

    foreach my $str (@port_seq_array) {

        if($str =~ m/^\s*config\s+port_security\s+ports\s+($PORTS)\s+.*state\s+(enable|disable).*/) {

            my $state = $2;
            my $portstr = $1;
            foreach my $port (ParsePorts($portstr)) {
                ${$hashref}->{port}->{$port}->{port_security} = $state;
                # ${$hashref}->{port}->{$port}->{description} = $desc_one;
                # print Dumper (%stuff_dict -> {$port});
                ${$hashref}->{port}->{$port} -> {'duplex'} = %stdict_duplex -> {$port} -> {'duplex'};
                ${$hashref}->{port}->{$port} -> {'speed_manual'} = %stdict_duplex -> {$port} -> {'speed_manual'};
                ${$hashref}->{port}->{$port} -> {description} = %stuff_dict -> {$port};
                ${$hashref}->{port}->{$port} -> {'ifOperStatus'} = 'null';
                ${$hashref}->{port}->{$port} -> {'ifAdminStatus'} = 'null';
                ${$hashref}->{port}->{$port} -> {'ifOutOctets'} = 'null';
                ${$hashref}->{port}->{$port} -> {'ifInOctets'} = 'null';
                ${$hashref}->{port}->{$port} -> {'media_type'} = 'null';

                $port =~ m/(\d+)/;
                $port =~ m/(\d+)\/(\d+)/;
                if ( !defined($2) ){
                    my $short_port = 0;
                }
                else{
                    ${$hashref}->{port}->{$port} -> {'traffic_here'} = 'null';
                    my $short_port = $2;
                    my $port_ifOperStatus = $out_json_snmp -> {'ifOperStatus'} -> {$short_port};
                    ${$hashref}->{port}->{$port} -> {'ifOperStatus'} = $port_ifOperStatus;
                    # print ($short_port. $port_ifOperStatus. "\n");
                    my $port_ifAdminStatus = $out_json_snmp -> {'ifAdminStatus'} -> {$short_port};
                    ${$hashref}->{port}->{$port} -> {'ifAdminStatus'} = $port_ifAdminStatus;
                    my $port_ifOutOctets = $out_json_snmp -> {'ifOutOctets'} -> {$short_port};
                    ${$hashref}->{port}->{$port} -> {'ifOutOctets'} = $port_ifOutOctets;
                    my $port_ifInOctets = $out_json_snmp -> {'ifInOctets'} -> {$short_port};
                    ${$hashref}->{port}->{$port} -> {'ifInOctets'} = $port_ifInOctets;
                    my $port_media_type= $out_json_snmp -> {'media_type'} -> {$short_port};
                    ${$hashref}->{port}->{$port} -> {'media_type'} = $port_media_type;
                }
            }
        }
    }

    # exit();
    return 1;
}

sub ParseStorm {
    my $port_num=shift;
    foreach my $storm   (@_) {
        $storm =~ m/config traffic control ($PORTS)/;
        my @array = ParsePorts($1);
        foreach my $num (@array) {
            if ($port_num eq $num) {
                $storm =~ m/action (drop|shutdown) /;
                my $action = $1;

                my $tres;
                my $tres_1;

                if ($storm =~ m/threshold (\d+)/){
                    $tres_1=int($1);
                }
                if (Translator::GetModel() eq 'DES-3526') {
                    $tres=int($tres_1)/500*100;
                } elsif ( Translator::GetModel() =~ m/DES/) {
                    $tres=int($tres_1)/64*100;
                } else {
                    $tres=int($tres_1)/64*100;
                }

                my $count = undef;
                if ($storm =~ m/countdown\s*(\d+)\s*/)
                {
                    $count = int($1);
                }

                my $interval = undef;
                if ($storm =~ m/interval (\d+) /)
                {
                    $interval=int($1);
                }

                if (defined $count && $action eq 'shutdown' && $count>0) {
                    #errord ("ACTION, TRES: ".$action, $tres,"\n");
                    return ($action,$tres);

                }elsif (Translator::GetModel() eq 'DES-3526' && $action ne 'drop'  )
                {
                    $action='shutdown';
                    return ($action,$tres);
                } else {
                    $action='drop';
                    return ($action,$tres);
                }
            }
        }
    }
}

sub ParseLag {
    my @array = @_;
    foreach (@array) {
        $_=~ s/,\s/,/g;
        if ($_=~ m/config\s+link_aggregation\s+group_id\s+\d+\s+master_port\s+(\d+)\s+ports\s+(.*?)\s+state\s+enable/) {
            my $lagname = $1;
            my @ports = ParsePortsString ($2);
            foreach my $p (@ports) {
                push @{$LAG->{$lagname}},$p;
            }
        }
    }
}

sub ParsePorts {
    my $string = shift;
    my @ports = ParsePortsString ($string);
    #LOOKING FOR EXISTING LAGS
    my %porthash = map {$_=>1} @ports;
    foreach my $p (@ports) {
        if (exists $LAG->{$p}) {
            foreach my $l (@{$LAG->{$p}}) {
                push @ports,$l if (!exists $porthash{$l});
            }
        }
    }
    my @eqm_ports;
    #Modify config port to eqm_port using delimiter

    foreach my $conf_port (@ports) {
        if ($eqm_delimiter ne '' && $conf_port !~ /$eqm_delimiter/) {
            if ($conf_port =~ m/[:\/]/) {
                $conf_port =~ s/[:\/]/$eqm_delimiter/
            } else {
                $conf_port = "$eqm_module_name$eqm_delimiter$conf_port";
            }
        }elsif ($eqm_delimiter eq '') {
            $conf_port =~ /^(\d+)$|^(\d+)[\/:](\d+)$/;
            if (defined $3) {
                $conf_port = $3;
            }else {
                $conf_port = $1;
            }
        }
        push @eqm_ports, Stack_process($conf_port);
    }
    return @eqm_ports;
}


sub ParsePorts2 {
    my $string = shift;
    my @ports = ParsePortsString ($string);
    #LOOKING FOR EXISTING LAGS
    my %porthash = map {$_=>1} @ports;
    foreach my $p (@ports) {
        # print "---------------------\n";
        # print $p;
        # print "=======================\n\n";
        #
        if (exists $LAG->{$p}) {
            foreach my $l (@{$LAG->{$p}}) {
                push @ports,$l if (!exists $porthash{$l});
            }
        }
    }
    return @ports;
}

sub Stack_process {
    my $port = shift;
    if (Translator::GetModel() =~ m/Stack/) {
        $port =~ /^(\d+)$|^(\d+)[\/:](\d+)$/;
        my $p = $1;
        if (defined $3 && !$eqm_modules) {
            $p = ($2-1)*64+$3;
            $p = "1$eqm_delimiter$p";
        } elsif (defined $3) {
            $port =~ s/[:\/]/$eqm_delimiter/;
            $p = $port;
        }

        return $p;
    }
    return $port;
}

sub ParsePortsString {
    #'1:24,2:(10,24),3:(11-22),44:55,2,1:1-1:5,2,3,7-9,10:(11),null,1:3-5'
    my $string = shift;
    my @ports;

    my @list;

    $string =~ s/(\d+:)(\d+-\d+)$/$1($2)/g; #replace 1:3-5 to 1:(3-5)
    $string =~ s/(\d+:)(\d+-\d+),\s*/$1($2),/g;

    while ($string =~ /(\d+:\(.*?\))|((\d+(:\d+)?)(-(\d+(:\d+)?))?)|null/g ) {
        my $str = $&;
        push @list,$str;
        $str =~ s/([()])/\\$1/g;
        $string =~ s/$str//;
    }
    foreach my $str (@list) {
        if ($str =~ m/((\d+):\((.*?)\))/ ){
            my $stack = $2;
            my $b = $3;
            my @array = split ',',$b;
            foreach my $a (@array) {
                $a =~ m/(\d+)(-(\d+))?/;
                if (defined $2){
                    foreach my $s ($1..$3) {
                        push @ports, "$stack:$s";
                    }
                }else{
                    push @ports, "$stack:$1";
                }
            }
        } elsif ($str =~ m/(((\d+):)*(\d+))(-((\d+):)*(\d+))*/){
            if (defined $5){
                foreach my $s ($4..$8) {
                    my $stack = '';
                    $stack = "$2" if (defined $2 && defined $6);
                    push @ports, "$stack$s";
                }
            } else {
                push @ports, "$str"
            }
        } elsif ($str =~ m/null/) {
            push @ports, '0';
        }
    }
    return @ports;
}




sub LoopDetect {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    if (my @grep_en_loop = grep {/^\s*enable loopdetect/} @str) {
        ${$hashref}->{'loopdetect'}->{'state'} = 'enable';
    } else {
        ${$hashref}->{'loopdetect'}->{'state'} = 'disable';
    }
    my @grep_rec_time = grep {/^\s*config\s+loopdetect.*recover_t\w+/} @str;
    $_=$grep_rec_time[0]=~ m/^\s*config\s+loopdetect.*recover_t\w+\s+(\d+)/;

    ${$hashref}->{'loopdetect'}->{'recover_time'} = $1;

    my @grep_interval = grep {/^\s*config\s+loopdetect.*interval/} @str;
    $_=$grep_interval[0]=~ m/^\s*config\s+loopdetect.*interval.*\s+(\d+)/;
    ${$hashref}->{'loopdetect'}->{'interval'} = $1;

    my $conf_ports;

    my @ports_loop = grep {/^\s*config loopdetect port.*state (enable|disable)d?/} @str;
    foreach my $str (@ports_loop){
        $str =~ m/^\s*config loopdetect port.*state (enable|disable)d?/;
        my $state = $1;
        foreach my $port (ParsePorts($str)) {
            ${$hashref}->{port}->{$port}->{'loopdetect'} = $state if (exists ${$hashref}->{port}->{$port});
        }
    }
    return 1;

}

sub STP {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    if (my @grep_en_stp = grep {/^\s*enable stp/} @str) {
        ${$hashref}->{stp}->{state} = 'enable';
    } else {
        ${$hashref}->{stp}->{state} = 'disable';
    }
    my @grep_stp_ver = grep {/^\s*config stp version (\w+)/} @str;
    $_=$grep_stp_ver[0]=~ m/^\s*config stp version (\w+)/;
    ${$hashref}->{stp}->{version} = $1;

    #config stp ports 1-24 externalCost auto edge true p2p auto state enable lbd enable

    my @state_array = grep {/^\s*config stp ports.*state (enable|disable).*/} @str;
    foreach my $str (@state_array) {
        $str =~ m/^\s*config stp ports\s+($PORTS)\s+.*state (enable|disable).*/;
        my $state = $2;
        my $portstr = $1;

        foreach my $port (ParsePorts($portstr)) {
            ${$hashref}->{port}->{$port}->{stp}->{state} = $state;
        }
    }

    my %hash =  ('true' => 'enable', 'false' => 'disable');

    #config stp ports 1-24 restricted_role true

    my @grep_stp_root_guard = grep {/^\s*config stp ports.*restricted_role/} @str;
    foreach my $str (@grep_stp_root_guard) {
        $str =~ m/config stp ports\s+($PORTS)\s.*restricted_role\s+(true|false)/;
        my $state = $hash{$2};
        my $portstr = $1;
        foreach my $port (ParsePorts($portstr)) {
            ${$hashref}->{port}->{$port}->{stp}->{'root-guard'} = $state;
        }
    }

    my @fbpdu_array = grep {/^\s*config stp ports.*fbpdu (enable|disable)/} @str;
    foreach my $str (@fbpdu_array) {
        $str =~ m/^\s*config stp ports\s+($PORTS)\s+.*bpdu (enable|disable)/;
        my $state = $2;
        my $portstr = $1;
        foreach my $port (ParsePorts($portstr)) {
            ${$hashref}->{port}->{$port}->{stp}->{'fbpdu'} = $state;
        }
    }

    #config stp ports 1-24 restricted_tcn true

    my @grep_stp_tcn = grep {/^\s*config stp ports.*restricted_tcn/} @str;
    foreach my $str (@grep_stp_tcn) {
        $str =~ m/config stp ports\s+($PORTS)\s.*restricted_tcn\s+(true|false)/;
        my $state = $hash{$2};
        my $portstr = $1;
        foreach my $port (ParsePorts($portstr)) {
            ${$hashref}->{port}->{$port}->{stp}->{'restricted_tcn'} = $state;
        }
    }
    #config stp ports 1-24 externalCost auto edge true p2p auto state enable lbd enable
    my @grep_stp_edge = grep {/^\s*config stp ports.*edge.*/} @str;
    foreach (@grep_stp_edge) {
        $_ =~ m/^\s*config stp ports\s+($PORTS)\s.*edge\s+(true|false|auto)\s+/;
        foreach my $port (ParsePorts($1)) {
            ${$hashref}->{port}->{$port}->{stp}->{'edge'} = $2;
        }
    }

    my @grep_stp_p2p = grep {/^\s*config stp ports.*p2p/} @str;
    foreach my $str (@grep_stp_p2p) {
        $str =~ m/config stp ports\s+($PORTS)\s+.*p2p\s+(true|false|auto)/;
        my $portstr = $1;
        my $state = $2;

        foreach my $port (ParsePorts($portstr)) {
            ${$hashref}->{port}->{$port}->{stp}->{'p2p'} = $2;
        }
    }
    return 1;
}

sub VLAN {
    #  my $start = my $start = Time::HiRes::gettimeofday();

    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    my $qinq = 0;

    if (!defined $LAG) {
        ParseLag(@str);
    }

    my @grep_vlan = grep {/^\s*create vlan.*tag.*/} @str;

    if (my @grepqinq = grep {/enable\s+qinq/} @str) {
        $qinq = 1;
    }
    my  $qinqports = {};
    if ($qinq) {
        my @grep = grep {/config\s+qinq/} @str;
        foreach my $s (@grep){
            $s =~ m/config\s+qinq\s+ports\s+($PORTS)\s+role\s+(uni|nni)(\smissdrop\s(enable|disable))?/;
            my $mode = $2;
            my $missdrop = 'disable';
            $missdrop = $4 if (defined $4);
            foreach (ParsePorts($1)){
                $qinqports -> {$_}->{mode} = $mode;
                $qinqports -> {$_}->{missdrop} = $missdrop if (defined $missdrop);
            }
        }
    }
    #msa-5889
    foreach my $found_vlan(@grep_vlan) {
        $_=$found_vlan=~ m/^\s*create vlan (.+) tag (\d+)/;
        my $name = $1;
        my $tag = $2;
        $name =~ s/"//g;    #"
        ${$hashref}->{vlan}->{$name} = $tag;
    }
    #  my $end = Time::HiRes::gettimeofday();
    #  print Dumper ($end - $start);

    my @transl_vlan = grep {/create vlan_translation/} @str;
    foreach my $str (@transl_vlan)  {
        $str =~ m/create\s+vlan_translation\s+ports\s+($PORTS)\s+(?:add\s+)?cvid\s+([\d,-]+)\s+(?:add\s+)?svid\s+(\d+)/;
        my $svid = $3;
        foreach my $port (ParsePorts($1)) {
            foreach my $cvid (ParseVlanStr($2)) {
                $cvid = '0' if ($cvid eq '1');
                push @{$qinqports->{$port}->{$svid}},$cvid ;
            }
        }
    }
    # $end = Time::HiRes::gettimeofday();
    # print Dumper ($end - $start);

    foreach my $conf_vlan ( grep {/config\s+vlan/} @str) {
        if ( $conf_vlan =~ m/config\s+vlan\s+(vlanid\s)?(.*)\s+add\s+(tagged|untagged)\s+($PORTS)\s*/) {
            #      if ($conf_vlan =~ /default/) { next }
            my @vlans;
            my $name = $2;
            my $istag = $3;
            my @ports = ParsePorts($4);
            $name =~ s/"//g;    #"
            $name =~ s/default/1/g;
            #Vlan Diapasone




            if ($name =~ m/[,-]/) {
                if (defined ${$hashref}->{vlan}->{$name}) {
                    push @vlans, $name
                } else {
                    @vlans = ParseVlanStr ($name);
                }
            } else {
                push @vlans, $name
            }
            foreach my $vlan (@vlans) {
                my $id;
                if (defined ${$hashref}->{vlan}->{$vlan}) {
                    $id = ${$hashref}->{vlan}->{$vlan};
                } else {
                    $id = $vlan;
                }
                foreach my $port (@ports) {

                    my @ids;
                    if ($qinq && $qinqports->{$port}->{mode} eq 'uni' && $istag eq 'untagged' && $qinqports->{$port}->{missdrop} eq 'disable'){
                        push @ids, "$id.*";
                    } elsif ($qinq && $qinqports->{$port}->{mode} eq 'uni' && $istag eq 'untagged' && $qinqports->{$port}->{missdrop} eq 'enable') {
                        if (exists $qinqports->{$port} && exists $qinqports->{$port}->{$id}){
                            foreach my $cv (@{$qinqports->{$port}->{$id}}) {
                                push @ids, "$id.$cv";
                            }
                        }
                    } else {
                        push @ids, $id;
                    }
                    foreach my $s (@ids) {
                        ${$hashref}->{port}->{$port}->{vlan}->{$s} = $istag;
                    }
                }
            }
        }
    }
    foreach my $port ( keys %{$qinqports} ) {
        foreach my $attr ( keys %{$qinqports->{$port}} ) {
            if ( $attr =~ /^\d+$/ ) {
                foreach my $vlan ( @{$qinqports->{$port}->{$attr}} ) {
                    ${$hashref}->{port}->{$port}->{vlan}->{"$attr.$vlan"} = 'untagged';
                }
            }
        }
    }
    my $member_port = '';
    my $source_port = '';
    my $vlan_name = '';
    my @grep_multi = grep {/^config igmp_snooping multicast_vlan (.+) add member_port (.+)/} @str;
    my @grep_name = grep {/^create igmp_snooping multicast_vlan\s+iptv\s+\d+/} @str;
    $grep_name[0] =~/^create igmp_snooping multicast_vlan iptv\s+(\d+)/;
    $vlan_name = $1;
    #  print('zzzzzz');

    #	print Dumper @str;


    my $multi = @grep_multi;
    if ($multi > 0) {
        my @temp = split(' ', $grep_multi[0]);

        $member_port= $temp[-1];
    }
    @grep_multi = grep {/^config igmp_snooping multicast_vlan (.+) add source_port (.+)/} @str;
    $multi = @grep_multi;
    if ($multi > 0) {
        my @temp = split(' ', $grep_multi[0]);
        $source_port = $temp[-1];

    }
    my @members_list = split(',', $member_port);
    my @members;

    foreach my $member_port (@members_list) {
        $member_port =~ m/(\d+)\:(\d+)\-(\d+)\:(\d+)/;
        $member_port =~ s/(\d+)\:(\d+)/$2/g;
        $member_port =~ m/(\d+)/;
        $member_port =~ m/(\d+)\-(\d+)/;
        my $member_start = 0;
        my $member_stop = 0;
        if ( !defined($2) ){
            $member_start = $member_port +0;
            $member_stop = $member_port +0;
        }
        else {
            $member_start = $1 + 0;
            $member_stop = $2 + 0;
        }
        for (my $i = $member_start; $i <= $member_stop; $i++) {
            push(@members, $i);
        }
    }

    my @sources_list = split(',', $source_port);
    my @sources;

    foreach my $source_port (@sources_list) {
        $source_port =~ m/(\d+)\:(\d+)\-(\d+)\:(\d+)/;
        $source_port =~ s/(\d+)\:(\d+)/$2/g;
        $source_port =~ m/(\d+)/;
        $source_port =~ m/(\d+)\-(\d+)/;

        my $source_start = 0;
        my $source_stop = 0;
        if ( !defined($2) ){
            $source_start = $source_port +0;
            $source_stop = $source_port +0;
        }
        else {
            $source_start = $1 + 0;
            $source_stop = $2 + 0;
        }
        for (my $i = $source_start; $i <= $source_stop; $i++) {
            push(@sources, $i);
        }
    }
    if ($vlan_name ne '') {
        foreach my $port ( sort keys %{${$hashref}->{port}} ) {
            my $iptv_port = $port;
            $iptv_port =~s/\d+\/(\d+)/$1/g;
            foreach my $s (@members) {
                if ($s == $iptv_port + 0) {
                    ${$hashref}->{port}->{$port}->{vlan}->{$vlan_name} = "untagged";
                    last;
                }
            }
            foreach my $s (@sources) {
                if ($s == $iptv_port + 0) {

                    ${$hashref}->{port}->{$port}->{vlan}->{$vlan_name} = "tagged";
                    last;
                }
            }
        }
    }


    my %vlans;
    foreach my $port ( sort keys %{${$hashref}->{port}} ) {
        if ( ${$hashref}->{port}->{$port}->{role_ru} =~ /^Абонентский/ && ( !exists ${$hashref}->{port}->{$port}->{usluga} || ${$hashref}->{port}->{$port}->{usluga} =~ /^физ\./ ) ) {
            foreach my $vlan ( keys %{${$hashref}->{port}->{$port}->{vlan}} ) {
                push @{$vlans{$vlan}}, $port;
            }
        }
    }
    my @wrong_vlans;
    foreach my $vlan ( keys %vlans ) {
        if ( scalar @{$vlans{$vlan}} > 1 ) {
            push @wrong_vlans, "$vlan - " . ( join ', ', sort @{$vlans{$vlan}} );
        }
    }
    if ( scalar @wrong_vlans > 0 ) {
        ${$hashref}->{pcv}->{vlans} = 'Wrong vlans: ' . ( join '; ', sort @wrong_vlans );
    }
    else {
        ${$hashref}->{pcv}->{vlans} = 'correct';
    }
    # print Dumper $hashref;

    return 1;
}

sub ParseVlanStr {
    my $str = shift;
    my @array;

    foreach my $s (split ',', $str) {
        $s =~ /(\d+)(-(\d+))?/;
        if (defined $2 && defined $3) {
            foreach ($1..$3) {
                push @array,$_;
            }
        } else {
            push @array,$1;
        }
    }
    return @array
}

sub ManagementACL {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;
    my $configstr = join "\n", @$configref;

    my $trusted_host_state = 'disable';

    # MANAGMENT ACL
    my @grep_mgmt_acl = grep {/^\s*create trusted_host/} @str;

    # create trusted_host network 109.195.0.8/29
    # create trusted_host host 109.195.0.100

    foreach my $found_mgmt_acl (@grep_mgmt_acl) {
        $_=$found_mgmt_acl =~ m/^\s*create trusted_host( \d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\/\d+| \d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/;
        ${$hashref}->{'acl'}->{$1} = 'trusted';
        $trusted_host_state = 'enable';
    }
    # END MANAGMENT AC

    # enable trusted_host
    if (my @grep_trust_enable = grep {/^\s*disable\s+trusted_host.*/} @str) {
        ${$hashref}->{'trusted_host'} = 'disable';
    } else {
        ${$hashref}->{'trusted_host'} = $trusted_host_state;
    }


    # disable web
    if (my @grep_web = grep {/^\s*enable\s+web.*/} @str) {
        my $web_port = '80';
        foreach my $s (@grep_web) {
            if ($s =~ /^\s*enable\s+web\s+(\d+).*/){
                $web_port = $1;
            }
        }
        if (my @grep_web_2 = grep {/^\s*disable\s+web.*/} @str) {
            ${$hashref}->{'management'}->{'web'}->{'state'} = 'disable';
        }
        else {
            ${$hashref}->{'management'}->{'web'}->{'state'} = 'enable';
        }
        ${$hashref}->{'management'}->{'web'}->{'port'} = $web_port;
    } else {
        ${$hashref}->{'management'}->{'web'}->{'state'} = 'disable';
    }

    # disable ssh
    if (my @grep_ssh = grep {/^\s*enable\s+ssh.*/} @str) {
        ${$hashref}->{'management'}->{'ssh'}->{'state'} = 'enable';
        my $ssh_port = '22';
        foreach my $s (@grep_ssh) {
            if ($s =~ /^\s*enable\s+ssh\s+(\d+).*/){
                $ssh_port = $1;
            }
        }
        ${$hashref}->{'management'}->{'ssh'}->{'port'} = $ssh_port;
    } else {
        ${$hashref}->{'management'}->{'ssh'}->{'state'} = 'disable';
    }

    # enable telnet 23
    if (my @grep_telnet = grep {/^\s*enable\s+telnet.*/} @str) {
        ${$hashref}->{'management'}->{'telnet'}->{'state'} = 'enable';
        my $telnet_port = '23';
        foreach my $s (@grep_telnet) {
            if ($s =~ /^\s*enable\s+telnet\s+(\d+).*/){
                $telnet_port = $1;
            }
        }
        ${$hashref}->{'management'}->{'telnet'}->{'port'} = $telnet_port;
    } else {
        ${$hashref}->{'management'}->{'telnet'}->{'state'} = 'disable';
    }

    # disable address_binding
    # enable address_binding roaming
    if (my @grep_address_binding = grep {/^\s*enable\s+address_binding.*/} @str) {
        ${$hashref}->{'address_binding'} = 'disable';
        # если есть строка кроме "enable address_binding roaming", то enable, иначе disable
        foreach my $str (@grep_address_binding) {
            if ($str !~ /^\s*enable\s+address_binding\s+roaming.*/){
                ${$hashref}->{'address_binding'} = 'enable';
            }
        }
    }


    # disable dhcp_relay
    if (my @grep_dhcp_relay = grep {/^\s*enable\s+dhcp_relay.*/} @str) {
        ${$hashref}->{'dhcp_relay'} = 'enable';
    } else {
        ${$hashref}->{'dhcp_relay'} = 'disable';
    }

    # disable dhcp_local_relay
    if (my @grep_dhcp_local_relay = grep {/^\s*enable\s+dhcp_local_relay.*/} @str) {
        ${$hashref}->{'dhcp_local_relay'} = 'enable';
    } else {
        ${$hashref}->{'dhcp_local_relay'} = 'disable';
    }

    # disable dhcpv6_relay
    if (my @grep_dhcpv6_relay = grep {/^\s*enable\s+dhcpv6_relay.*/} @str) {
        ${$hashref}->{'dhcpv6_relay'} = 'enable';
    } else {
        ${$hashref}->{'dhcpv6_relay'} = 'disable';
    }

    # disable gvrp
    if (my @grep_gvrp = grep {/^\s*enable\s+gvrp.*/} @str) {
        ${$hashref}->{'gvrp'} = 'enable';
    } else {
        ${$hashref}->{'gvrp'} = 'disable';
    }

    # disable rmon
    if (my @grep_rmon = grep {/^\s*enable\s+rmon.*/} @str) {
        ${$hashref}->{'rmon'} = 'enable';
    } else {
        ${$hashref}->{'rmon'} = 'disable';
    }

    # disable igmp_snooping
    if (my @grep_igmp_snooping = grep {/^\s*enable\s+igmp_snooping.*/} @str) {
        ${$hashref}->{'igmp_snooping'} = 'enable';
    } else {
        ${$hashref}->{'igmp_snooping'} = 'disable';
    }

    # disable mld_snooping
    if (my @grep_mld_snooping = grep {/^\s*enable\s+mld_snooping.*/} @str) {
        ${$hashref}->{'mld_snooping'} = 'enable';
    } else {
        ${$hashref}->{'mld_snooping'} = 'disable';
    }

    # disable 802.1x
    if (my @grep_8021x = grep {/^\s*enable\s+802\.1x.*/} @str) {
        ${$hashref}->{'p8021x'} = 'enable';
    } else {
        ${$hashref}->{'p8021x'} = 'disable';
    }

    # disable flood_fdb
    if (my @grep_flood_fdb = grep {/^\s*enable\s+flood_fdb.*/} @str) {
        ${$hashref}->{'flood_fdb'} = 'enable';
    } else {
        ${$hashref}->{'flood_fdb'} = 'disable';
    }

    # enable password encryption
    if (my @grep_password_encryption = grep {/^\s*enable\s+password\s+encryption.*/} @str) {
        ${$hashref}->{'password_encryption'} = 'enable';
    } else {
        ${$hashref}->{'password_encryption'} = 'disable';
    }

    # disable smtp
    if (my @grep_smtp = grep {/^\s*enable\s+smtp.*/} @str) {
        ${$hashref}->{'smtp'} = 'enable';
    } else {
        ${$hashref}->{'smtp'} = 'disable';
    }

    # disable sim
    if (my @grep_sim = grep {/^\s*enable\s+sim.*/} @str) {
        ${$hashref}->{'sim'} = 'enable';
    } else {
        ${$hashref}->{'sim'} = 'disable';
    }

    # disable erps
    if (my @grep_erps = grep {/^\s*enable\s+erps.*/} @str) {
        ${$hashref}->{'erps'} = 'enable';
    } else {
        ${$hashref}->{'erps'} = 'disable';
    }

    # disable autoconfig
    if (my @grep_autoconfig = grep {/^\s*enable\s+autoconfig.*/} @str) {
        ${$hashref}->{'autoconfig'} = 'enable';
    } else {
        ${$hashref}->{'autoconfig'} = 'disable';
    }

    # config safeguard_engine state disable
    if (my @grep_safeguard_engine = grep {/^\s*config\s+safeguard_engine\s+state\s+enable.*/} @str) {
        ${$hashref}->{'safeguard_engine'} = 'enable';
    } else {
        ${$hashref}->{'safeguard_engine'} = 'disable';
    }

    # config dos_prevention * state disable
    if (my @grep_dos_prevention = grep {/^\s*config\s+dos_prevention\s+.*state\s+enable.*/} @str) {
        ${$hashref}->{'dos_prevention'} = 'enable';
    } else {
        ${$hashref}->{'dos_prevention'} = 'disable';
    }

    # config ports all learning enable
    # config ports all mdix auto
    # config duld ports 1-28 state disable
    # config traffic trap ??
    # disable command logging ??
    #
    # config ipif System vlan qnqmng ipaddress 10.242.148.10/24 state enable
    # config ipif System dhcp_option12 state disable
    #


    return 1;
}


sub SNMP {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    #  enable snmp linkchange_traps
    #  config snmp linkchange_traps ports all enable

    # default value
    foreach my $s (keys %{${$hashref}->{port}}) {
        ${$hashref}->{port}->{$s}->{snmp}->{linkchange_traps} = 'disable';
    }

    if (!(my @grep_snmp_trap_all = grep {/^\s*disable\s+snmp\s+traps.*/} @str) && (my @grep_snmp_trap = grep {/^\s*enable\s+snmp\s+linkchange_traps.*/} @str)) {
        ${$hashref}->{'snmp'}->{'linkchange_traps'} = 'enable';
        if (my @grep_snmp_trap_port1 = grep {/^\s*config\s+snmp\s+linkchange_traps\s+ports\s+all\s+enable.*/} @str) {
            foreach my $s (keys %{${$hashref}->{port}}) {
                ${$hashref}->{port}->{$s}->{snmp}->{linkchange_traps} = 'enable';
            }
        }
        foreach my $s (my @grep_snmp_trap_port2 = grep {/^\s*config\s+snmp\s+linkchange_traps\s+ports\s+($PORTS).*/} @str) {
            if ($s =~ /config\s+snmp\s+linkchange_traps\s+ports\s+($PORTS)\s+(enable|disable).*/) {
                my $portstr = $1;
                my $state = $2;
                foreach my $port (ParsePorts($portstr)) {
                    ${$hashref}->{port}->{$port}->{snmp}->{linkchange_traps} = $state;
                }
            }
        }
    } else {
        ${$hashref}->{'snmp'}->{'linkchange_traps'} = 'disable';
    }


    # create snmp host IP-EQM v2c <COMMUNITY>

    my $host_id = 1;
    foreach my $s (my @grep_snmp_host = grep {/^\s*create\s+snmp\s+host\s+(.+)\s+v(.+)\s+(.+)\s*/} @str) {
        if ($s =~ /create\s+snmp\s+host\s+(.+)\s+v(.+)\s+(.+)\s*/) {
            my $ip = $1;
            my $version = $2;
            my $community = $3;
            ${$hashref}->{'snmp'}->{'host'}->{$host_id}->{'ip'} = $ip;
            ${$hashref}->{'snmp'}->{'host'}->{$host_id}->{'version'} = $version;
            ${$hashref}->{'snmp'}->{'host'}->{$host_id}->{'community'} = $community;
            $host_id++;
        }
    }


    if (my @grep_snmp_trap = grep {/^\s*enable\s+snmp\s+traps/} @str) {
        ${$hashref}->{'snmp'}->{'traps'} = 'enable';
    } else {
        ${$hashref}->{'snmp'}->{'traps'} = 'disable';
    }
    if (my @grep_snmp_sysname = grep {/^\s*config\s+snmp\s+system_name/} @str) {
        $_=$grep_snmp_sysname[0] =~ m/^\s*config\s+snmp\s+system_name (.+)/;
        ${$hashref}->{'snmp'}->{'systemname'} = $1;  }

    # config snmp system_location ER-Telecom_Lipetsk
    if (my @grep_snmp_sysloc = grep {/^\s*config\s+snmp\s+system_location/} @str) {
        $_=$grep_snmp_sysloc[0] =~ m/^\s*config snmp system_location (.+)/;
        ${$hashref}->{'snmp'}->{'systemlocation'} = $1;
    }
    # END MANAGMENT SNMP

    my %level = (
        'read_write' => 'rw',
        'read_only' => 'ro',
        'ReadWrite' => 'rw',
        'ReadOnly' => 'ro'
    );

    my $community = {};
    foreach my $s (my @grep_snmp_comm = grep {/create\s+snmp\s+community/} @str) {
        if ($s =~ /create\s+snmp\s+community\s+([\d\w_]*).*\s+(read_write|read_only|ReadOnly|ReadWrite)/){
            $community->{$1} = $2 if (defined $1 and defined $2);
        }
    }
    foreach my $community_name ( keys %{$community}) {
        ${$hashref}->{snmp}->{community}->{$community_name} = $level{$community->{$community_name}};
    }
    return 1;
}


sub StormControl {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    foreach my $mode ('broadcast','unicast','multicast') {
        my @array = grep {/config traffic control.*$mode/} @str;
        foreach my $a (@array) {
            $a =~ m/^\s*config\s+traffic\s+control\s+($PORTS).*$mode\s+(enable|disable).*/;
            my $ports_tc =$1;
            my $status =$2;
            if (Translator::GetModel() =~ m/3526/){
                if ($ports_tc eq '4-5'){
                    $ports_tc='25-26';
                }
            }
            foreach my $port (ParsePorts($ports_tc)) {
                if (exists ${$hashref}->{port}->{$port}) {
                    my @res=ParseStorm($port,$a);
                    ${$hashref}->{port}->{$port}->{'storm'}->{$mode} -> {'status'} = $status;
                    ${$hashref}->{port}->{$port}->{'storm'}->{$mode} -> {'level'} = $res[1];
                    ${$hashref}->{port}->{$port}->{'storm'}->{$mode} -> {'action'} = $res[0];
                }
            }
        }
    }
    return 1;
}

sub TrafficSegmentation {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    no strict;

    my @ports;
    foreach my $port_strings ( grep {/^\s*config ports ([-,\d]+) .*/} @str ) {
        push @ports, $1 if $port_strings =~ /^\s*config ports ([-,\d]+) .*/;
    }
    my $ports = join ',', @ports;
    @ports = ParsePorts2($ports);
    my $max_port = max(@ports);

    my @grep_traf_seg = grep {/^\s*config traffic_segmentation (-|,|\d)+ .*/} @str;

    my %hashports;
    foreach my $segm_strings (@grep_traf_seg) {
        $_=$segm_strings=~ m/($PORTS)\s+forward_list\s+($PORTS|null|all)/;
        my @lp = ParsePorts2($1);
        my @rp = $2 eq 'all' ? ParsePorts2('1-' . $max_port) : ParsePorts2($2);
        foreach my $left_port (@lp) {
            foreach my $right_port (@rp) {
                my @left_prt = ParsePorts($left_port);
                my $left_p = $left_prt[0];
                if ($right_port != 0) {
                    my @right_prt = ParsePorts($right_port);
                    my $right_p = $right_prt[0];
                    $hashports{$left_p}{links}{$right_p} = 1;
                } else {
                    $hashports{$left_p}{links} = 0;
                }
            }
        }
    }

    my $max = -1;
    my %uplinks;
    foreach my $port (keys %hashports) {
        if (($hashports{$port}{links} == 0) || !(exists $hashports{$port})) {
            $hashports{$port}{type} = 'null';
        } else {
            my $count = scalar keys %{$hashports{$port}{links}};
            if ($count < $max) {
                $hashports{$port}{type} = 'downlink';
            } elsif ($count == $max) {
                $hashports{$port}{type} = 'uplink';
                $uplinks{$port} = 1;
            } elsif ($count > $max) {
                $max = $count;
                foreach my $uplink (keys %uplinks) {
                    $hashports{$uplink}{type} = 'downlink';
                    delete $uplinks{$uplink};
                }
                $hashports{$port}{type} = 'uplink';
                $uplinks{$port} = 1;
            }
        }
    }

    undef %uplinks;
    foreach my $port (keys %{${$hashref}->{port}}) {
        if (${$hashref}->{port}->{$port}->{type} eq 'uplink') {
            $uplinks{$port} = 1;
        }
    }

    my $ucount = scalar keys %uplinks;
    foreach my $port (keys %hashports) {
        my $forwarding = 1;
        my $count = scalar keys %{$hashports{$port}{links}};
        if (${$hashref}->{port}->{$port}->{role} =~ /common|PA_CLNT|PM_NOCTL|PA_PPPOE|PA_IPOE|PA_L2|PM_L2/) {
            foreach my $uport (keys %uplinks) {
                $forwarding = $forwarding && ((exists $hashports{$port}{links}{$uport}) && ($count >= $ucount));
            }
        } elsif (exists $uplinks{$port}) {
            foreach my $uport (keys %uplinks) {
                $forwarding = $forwarding && ((exists $hashports{$port}{links}{$uport}) || ($port eq $uport));
            }
        }
        ${$hashref}->{port}->{$port}->{'traffic_segment'}->{'type'} = $hashports{$port}{type};
        ${$hashref}->{port}->{$port}->{'traffic_segment'}->{'forwarding'} = $forwarding ? 'correct' : 'wrong';
    }

    use strict;
    return 1;
}

sub MacNotification {
    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    my $def_state;
    my @cfg = grep {'mac_notification'} @str;
    foreach my $s (keys %{${$hashref}->{port}}) {
        ${$hashref}->{port}->{$s}->{snmp}->{mac_notification} = 'disable';
    }

    foreach my $str (@cfg) {
        if ($str =~ m/(enable|disable)\s+mac_notification/) {
            $def_state = $1;
        }elsif ( $str =~ /config\s+mac_notification\s+ports\s+($PORTS)\s+(enable|disable)/) {
            my $portstr = $1;
            my $state = $2;
            foreach my $port  (ParsePorts($portstr)) {
                if ($def_state eq 'enable'){
                    ${$hashref}->{port}->{$port}->{snmp}->{mac_notification} = $state;
                } else {
                    ${$hashref}->{port}->{$port}->{snmp}->{mac_notification} = 'disable';
                }
            }
        }
    }
}

sub Radius {
    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    if (my @grep_en_loop = grep {/^\s*enable\s+authen_policy/} @str) {
        ${$hashref}->{'radius'}->{'state'} = 'enable';
    } else {
        ${$hashref}->{'radius'}->{'state'} = 'disable';
    }

    my @radius_array = grep {/^\s*config\s+\w+\s+server_group\s+radius\s+add\s+server_host.*protocol\s+radius.*/} @str;
    foreach my $str (@radius_array) {
        $str =~ m/^\s*config\s+\w+\s+server_group\s+radius\s+add\s+server_host\s+(\d+\.\d+\.\d+\.\d+)\s+.*protocol\s+radius.*/;
        my $radius_ip = $1;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'state'} = 'enable';
    }

    my @radius_create_array = grep {/^\s*create\s+authen\s+server_host.*protocol\s+radius port\s+\d+\s+key.*timeout\s+\d+\s+retransmit\s+\d+.*/} @str;
    foreach my $str (@radius_create_array) {
        $str =~ m/^\s*create\s+authen\s+server_host\s+(\d+\.\d+\.\d+\.\d+)\s+.*protocol\s+radius\s+port\s+(\d+)\s+.*key\s+(.+)\s+.*timeout\s+(\d+)\s+.*retransmit\s+(\d+).*/;
        my $radius_ip = $1;
        my $radius_port = $2;
        my $radius_key = $3;
        my $radius_timeout = $4;
        my $radius_retransmit = $5;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'port'} = $radius_port;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'key'} = $radius_key;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'timeout'} = $radius_timeout;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'retransmit'} = $radius_retransmit;
    }

    my @radius_create_array1 = grep {/^\s*create\s+radius\s+server_host.*auth_port\s+\d+\s+acct_port\s+\d+\s+\w*key.*timeout\s+\d+\s+retransmit\s+\d+.*/} @str;
    foreach my $str (@radius_create_array1) {
        $str =~ m/^\s*create\s+radius\s+server_host\s+(\d+\.\d+\.\d+\.\d+)\s+auth_port\s+(\d+)\s+acct_port\s+(\d+)\s+\w*key\s+(.+)\s+timeout\s+(\d+)\s+.*retransmit\s+(\d+).*/;
        my $radius_ip = $1;
        my $radius_port = $2;
        my $radius_acc_port = $3;
        my $radius_key = $4;
        my $radius_timeout = $5;
        my $radius_retransmit = $6;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'port'} = $radius_port;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'key'} = $radius_key;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'timeout'} = $radius_timeout;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'retransmit'} = $radius_retransmit;
        ${$hashref}->{'radius'}->{'server'}->{$radius_ip}->{'acc_port'} = $radius_acc_port;
    }

    my @config_authen_parameter_attempt = grep {/^\s*config\s+authen\s+parameter\s+attempt.*/} @str;
    foreach my $str (@config_authen_parameter_attempt) {
        $str =~ m/^\s*config\s+authen\s+parameter\s+attempt\s+(\d+).*/;
        my $parameter_attempt = $1;
        ${$hashref}->{'radius'}->{'parameter_attempt'} = $parameter_attempt;
    }

    my @config_authen_parameter_response_timeout = grep {/^\s*config\s+authen\s+parameter\s+response_timeout.*/} @str;
    foreach my $str (@config_authen_parameter_response_timeout) {
        $str =~ m/^\s*config\s+authen\s+parameter\s+response_timeout\s+(\d+).*/;
        my $response_timeout = $1;
        ${$hashref}->{'radius'}->{'response_timeout'} = $response_timeout;
    }

    my @config_authen_method_list_name = grep {/^\s*config\s+authen_(enable|login)\s+(method_list_name\s+)*\w+\s+method\s+.*/} @str;
    foreach my $str (@config_authen_method_list_name) {
        $str =~ m/^\s*config\s+authen_(enable|login)\s+(method_list_name\s+)*(\w+)\s+method\s+(.*)/;
        my $authen_type = $1;
        my $authen_method_name = $3;
        my $authen_method_list = $4;
        ${$hashref}->{'radius'}->{"${authen_type}_method_list"}->{$authen_method_name} = $authen_method_list;
    }

    my @config_authen_application_login = grep {/^\s*config\s+authen\s+application\s+\w+\s+(enable|login)\s.*/} @str;
    foreach my $str (@config_authen_application_login) {
        $str =~ m/^\s*config\s+authen\s+application\s+(\w+)\s+(enable|login)\s+(method_list_name\s+)*(\w+).*/;
        my $application_name = $1;
        my $login_enable = $2;
        my $application_method = $4;
        ${$hashref}->{'radius'}->{"app_${login_enable}_method_list"}->{$application_name} = $application_method;
        ${$hashref}->{'radius'}->{"app_${login_enable}_method"}->{$application_name} = ${$hashref}->{'radius'}->{"${login_enable}_method_list"}->{$application_method};
    }

    my @config_admin_local_enable = grep {/^\s*config\s+admin\s+local_enable.*/} @str;
    foreach my $str1 (@config_admin_local_enable) {
        $str1 =~ m/^\s*config\s+admin\s+local_enable\s*(.*)\s*/;
        if ($1 eq "") {
            my $enable_password;
            my $enable_password_confirm;
            my $i = 0;
            while ( $i < scalar @str ) {
                if ( $str[$i] =~ /^\s*config\s+admin\s+local_enable.*/ ) {
                    $i++;
                    while ( $i < scalar @str && $str[$i] =~ /^\s*$/ ) {
                        $i++;
                    }
                    $enable_password = $str[$i] if ( defined $str[$i] );
                    $i++;
                    while ( $i < scalar @str && $str[$i] =~ /^\s*$/ ) {
                        $i++;
                    }
                    $enable_password_confirm = $str[$i] if ( defined $str[$i] );

                    if ($enable_password eq $enable_password_confirm) {
                        ${$hashref}->{'radius'}->{'enable_password'} = $enable_password;
                    } else {
                        ${$hashref}->{'radius'}->{'enable_password'} = "";
                    }
                    last;
                }
                $i++;
            }
        } else {
            ${$hashref}->{'radius'}->{'enable_password'} = $1;
        }
    }

    return 1;

}

sub NTP {
    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    if (my @grep_en_sntp = grep {/^\s*enable\s+sntp.*/} @str) {
        ${$hashref}->{'ntp'}->{'state'} = 'enable';
    } else {
        ${$hashref}->{'ntp'}->{'state'} = 'disable';
    }

    if (my @grep_conf_tz = grep {/^\s*config\s+time_zone.*/} @str) {
        foreach my $str (@grep_conf_tz) {
            if ($str =~ m/^\s*config\s+time_zone\s+operator\s*(.*)\s*hour\s+(\d+)\s+min\s+(\d+).*/) {
                my $time_zone_min = $3;
                my $operator = $1;
                my $time_zone = $2;
                if ($time_zone_min eq "0") {
                    my $time_zone = $time_zone;
                } else {
                    my $time_zone = ${time_zone}."-".${time_zone_min};
                }
                if ($operator eq "-") {
                    ${time_zone} = "-".${time_zone};
                }
                ${$hashref}->{'ntp'}->{'time_zone'} = $time_zone;
            }
        }
    } else {
        ${$hashref}->{'ntp'}->{'time_zone'} = "0";
    }

    if (my @grep_conf_sntp = grep {/^\s*config\s+sntp.*/} @str) {
        foreach my $str (@grep_conf_sntp) {
            if ($str =~ m/^\s*config\s+sntp\s+primary\s+(\d+\.\d+\.\d+\.\d+)\s+secondary\s+(\d+\.\d+\.\d+\.\d+)\s+poll-interval\s+(\d+)*/) {
                my $ntp_server1 = $1;
                my $ntp_server2 = $2;
                my $poll_interval = $3;
                ${$hashref}->{'ntp'}->{'server1'} = $ntp_server1;
                ${$hashref}->{'ntp'}->{'server2'} = $ntp_server2;
                ${$hashref}->{'ntp'}->{'poll_interval'} = $poll_interval;
            }
        }
    } else {
        ${$hashref}->{'ntp'}->{'server1'} = "";
        ${$hashref}->{'ntp'}->{'server2'} = "";
        ${$hashref}->{'ntp'}->{'poll_interval'} = "";
    }

    return 1;
}

sub SYSLOG {
    my $mod = shift;
    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    #enable syslog

    if (my @grep_en_syslog = grep {/^\s*enable\s+syslog.*/} @str) {
        ${$hashref}->{'syslog'}->{'state'} = 'enable';
    } else {
        ${$hashref}->{'syslog'}->{'state'} = 'disable';
    }

    my $hostname = `uname -n`;
    $hostname =~ s/[\n\r]//g;
    my $hent = gethostbyname($hostname);
    my $addr_ref  = $hent->addr_list;
    my @addresses = map { inet_ntoa($_) } @$addr_ref;
    foreach my $address ( @addresses ) {
        ${$hashref}->{'syslog'}->{'server'}->{$address}->{'state'} = "disable";
    }

    #create syslog host 1 ipaddress <EQM-IP> severity all facility local0 udp_port 514 state enable

    if (my @grep_conf_syslog = grep {/^\s*create\s+syslog\s+.*host\s+\d+\s+.*/} @str) {
        foreach my $str (@grep_conf_syslog) {
            if ($str =~ m/^\s*create\s+syslog\s+.*ipaddress\s+(\d+\.\d+\.\d+\.\d+).*/) {
                my $host = $1;
                if ($str =~ m/^\s*create\s+syslog\s+.*severity\s+(\w+).*/) {
                    my $severity = $1;
                    ${$hashref}->{'syslog'}->{'server'}->{$host}->{'severity'} = $severity
                }
                if ($str =~ m/^\s*create\s+syslog\s+.*facility\s+local(\d+).*/) {
                    my $facility = $1;
                    ${$hashref}->{'syslog'}->{'server'}->{$host}->{'facility'} = $facility;
                }
                if ($str =~ m/^\s*create\s+syslog\s+.*udp_port\s+(\d+).*/) {
                    my $port = $1;
                    ${$hashref}->{'syslog'}->{'server'}->{$host}->{'port'} = $port;
                }
                if ($str =~ m/^\s*create\s+syslog\s+.*state\s+(enable|disable).*/) {
                    my $state = $1;
                    ${$hashref}->{'syslog'}->{'server'}->{$host}->{'state'} = $state;
                }
            }
        }
    }

    return 1;
}

sub Jumbo {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    if (my @grep_en_jumbo = grep {/enable\s+jumbo_frame/} @str) {
        ${$hashref}->{'jumbo'} = 'enable';
    } else {
        ${$hashref}->{'jumbo'} = 'disable';
    }
    return 1;
}

sub IPTV {
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;

    my @ports;
    @ports = keys %{${$hashref}->{port}};
    foreach my $port ( @ports ) {
        ${$hashref}->{port}->{$port}->{'iptv'}->{'filter_mode'} = 'none';
    }
    if ( my @grep_conf_multicast = grep {/^\s*config\s+multicast\s+/} @str ) {
        foreach my $str ( @grep_conf_multicast ) {
            if ( $str =~ /^\s*config\s+multicast\s+(?:port_)?filter(?:ing_mode)?\s+($PORTS|all)\s+(filter|forward)(?:_(?:unregistered|all)_groups)?\s*$/ ) {
                my $ports_str = $1;
                my $mode = $2;
                if ( $ports_str =~ /$PORTS/ ) {
                    @ports = ParsePorts($ports_str);
                }
                else {
                    @ports = keys %{${$hashref}->{port}};
                }
                foreach my $port ( @ports ) {
                    ${$hashref}->{port}->{$port}->{'iptv'}->{'filter_mode'} = $mode;
                }
            }
            elsif ( $str =~ /^\s*config\s+multicast\s+(vlan_)?filter(ing_mode)?\s+(vlan\s+iptv|vlanid\s+4024)\s+(filter|forward)(_unregistered_groups)?\s*$/ ) {
                @ports = keys %{${$hashref}->{port}};
                foreach my $port ( @ports ) {
                    my $role = ${$hashref}->{port}->{$port}->{'role'};
                    if ( $role eq 'PA_CLNT' || $role eq 'PM_NOCTL' || $role eq 'PA_PPPOE' || $role eq 'PA_IPOE' ) {
                        ${$hashref}->{port}->{$port}->{'iptv'}->{'filter_mode'} = 'filter';
                    }
                    elsif ( $role eq 'PA_RS' || $role eq 'PA_RSUL' || $role eq 'PA_L2' || $role eq 'PM_L2' ) {
                        ${$hashref}->{port}->{$port}->{'iptv'}->{'filter_mode'} = 'forward';
                    }
                }
            }
        }
    }

    ${$hashref}->{'iptv'}->{'profile235'} = 'correct';
    if (not grep {/^\s*(config|create)\s+(mcast_filter_profile|multicast_range)\s+(?:profile_id\s+(\d+)\s+add|base\s+from)\s+235\.10\.10\.0(\-| to )235\.10\.10\.255\s*$/} @str){
        ${$hashref}->{'iptv'}->{'profile235'} = 'incorrect';
    }
    if (not grep {/^\s*(config|create)\s+(mcast_filter_profile|multicast_range)\s+(?:profile_id\s+(\d+)\s+add|more\s+from)\s+235\.10\.11\.0(\-| to )235\.10\.11\.255\s*$/} @str){
        ${$hashref}->{'iptv'}->{'profile235'} = 'incorrect';
    }

    if ( my @grep_mcast_filter_profile = grep {/mcast_filter_profile/} @str ) {
        foreach my $str ( @grep_mcast_filter_profile ) {
            if ( $str =~ /^\s*create\s+mcast_filter_profile\s+(?:ipv4\s+)?profile_id\s+(\d+)\s+profile_name\s+(service|streaming)\s*$/ ) {
                ${$hashref}->{'iptv'}->{'profile'}->{$1}->{'name'} = $2;
            }
            if ( $str =~ /^\s*config\s+mcast_filter_profile\s+profile_id\s+(\d+)\s+add\s+(\d+\.\d+\.\d+\.\d+)(?:[\s\-]+)?(\d+\.\d+\.\d+\.\d+)?\s*$/ ) {
                ${$hashref}->{'iptv'}->{'profile'}->{$1}->{'host1'} = $2;
                if ( defined $3 ) {
                    ${$hashref}->{'iptv'}->{'profile'}->{$1}->{'host2'} = $3;
                }
                else {
                    ${$hashref}->{'iptv'}->{'profile'}->{$1}->{'host2'} = $2;
                }
            }
        }
    }

    @ports = keys %{${$hashref}->{port}};
    foreach my $port ( @ports ) {
        foreach my $profile ( keys %{${$hashref}->{'iptv'}->{'profile'}} ) {
            ${$hashref}->{port}->{$port}->{'iptv'}->{'profile'}->{$profile} = 'disable';
        }
    }
    if ( my @grep_limited_multicast_addr = grep {/limited_multicast_addr/} @str ) {
        foreach my $str ( @grep_limited_multicast_addr ) {
            if ( $str =~ /^\s*config\s+limited_multicast_addr\s+ports\s+($PORTS)\s+(?:ipv4\s+)?(add|delete)\s+profile_id\s+(\d+)\s*$/ ) {
                @ports = ParsePorts($1);
                foreach my $port ( @ports ) {
                    if ( $2 eq 'add' ) {
                        ${$hashref}->{port}->{$port}->{'iptv'}->{'profile'}->{$3} = 'enable';
                    }
                    elsif ( $2 eq 'delete' ) {
                        ${$hashref}->{port}->{$port}->{'iptv'}->{'profile'}->{$3} = 'disable';
                    }
                }
            }
        }
    }

    @ports = keys %{${$hashref}->{port}};
    foreach my $port ( @ports ) {
        ${$hashref}->{port}->{$port}->{'iptv'}->{'max_mcast_group'}->{'iptv4'} = 'none';
        ${$hashref}->{port}->{$port}->{'iptv'}->{'max_mcast_group'}->{'iptv6'} = 'none';
    }
    if ( my @grep_max_mcast_group = grep {/max_mcast_group/} @str ) {
        foreach my $str ( @grep_max_mcast_group ) {
            if ( $str =~ /^\s*config\s+max_mcast_group\s+port(?:s)?\s+($PORTS)\s+(?:ipv4\s+)?max_group\s+(\d+)(?:\s+action\s+(?:drop|replace))?\s*$/ ) {
                @ports = ParsePorts($1);
                foreach my $port ( @ports ) {
                    ${$hashref}->{port}->{$port}->{'iptv'}->{'max_mcast_group'}->{'iptv4'} = $2;
                }
            }
            if ( $str =~ /^\s*config\s+max_mcast_group\s+port(?:s)?\s+($PORTS)\s+ipv6\+max_group\s+(\d+)(?:\s+action\s+(?:drop|replace))?\s*$/ ) {
                @ports = ParsePorts($1);
                foreach my $port ( @ports ) {
                    ${$hashref}->{port}->{$port}->{'iptv'}->{'max_mcast_group'}->{'iptv6'} = $2;
                }
            }
        }
    }

    if ( my @grep_igmp_snooping = grep {/igmp_snooping/} @str ) {
        if ( grep {/^\s*enable\s+igmp_snooping\s*$/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'state'} = 'enable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'state'} = 'disable';
        }

        if ( my @grep = grep {/^\s*config\s+igmp_snooping\s+data_driven_learning\s+max_learned_entry\s+(\d+)\s*$/} @grep_igmp_snooping ) {
            $grep[0] =~ /^\s*config\s+igmp_snooping\s+data_driven_learning\s+max_learned_entry\s+(\d+)\s*$/;
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'max_learned_entry'} = $1;
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'max_learned_entry'} = 'none';
        }

        if ( grep {/^\s*enable\s+igmp_snooping\s+multicast_vlan\s*$/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'state'} = 'enable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'state'} = 'disable';
        }

        if ( my @grep = grep {/^\s*create\s+igmp_snooping\s+multicast_vlan\s+iptv\s+(\d+)\s*$/} @grep_igmp_snooping ) {
            $grep[0] =~ /^\s*create\s+igmp_snooping\s+multicast_vlan\s+iptv\s+(\d+)\s*$/;
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'vlan'} = $1;
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'vlan'} = 'none';
        }

        if ( grep {/^\s*(?:create|config)\s+igmp_snooping\s+multicast_vlan\s+iptv\s+state\s+enable.*$/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'state'} = 'enable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'state'} = 'disable';
        }

        if ( my @grep = grep {/replace_source_ip\s+(\d+\.\d+\.\d+\.\d+)/} @grep_igmp_snooping ) {
            $grep[0] =~ /replace_source_ip\s+(\d+\.\d+\.\d+\.\d+)/;
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'replace_source_ip'} = $1;
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'multicast_vlan'}->{'iptv'}->{'replace_source_ip'} = 'none';
        }

        @ports = keys %{${$hashref}->{port}};
        foreach my $port ( @ports ) {
            ${$hashref}->{port}->{$port}->{'iptv'}->{'multicast_vlan'}->{'port_type'} = 'none';
        }
        if ( my @grep = grep {/member_port\s+($PORTS)/} @grep_igmp_snooping ) {
            foreach my $str ( @grep ) {
                $str =~ /member_port\s+($PORTS)/;
                @ports = ParsePorts($1);
                foreach my $port ( @ports ) {
                    ${$hashref}->{port}->{$port}->{'iptv'}->{'multicast_vlan'}->{'port_type'} = 'member';
                }
            }
        }
        if ( my @grep = grep {/source_port\s+($PORTS)/} @grep_igmp_snooping ) {
            foreach my $str ( @grep ) {
                $str =~ /source_port\s+($PORTS)/;
                @ports = ParsePorts($1);
                foreach my $port ( @ports ) {
                    ${$hashref}->{port}->{$port}->{'iptv'}->{'multicast_vlan'}->{'port_type'} = 'source';
                }
            }
        }

        if ( grep {/^\s*config\s+igmp_snooping\s+querier\s+.*\s+state\s+disable.*/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'querier'}->{'state'} = 'disable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'querier'}->{'state'} = 'enable';
        }

        if ( grep {/^\s*config\s+igmp_snooping\s+data_driven_learning\s+(?:vlanid|vlan_name)\s+(?:4024|iptv)\s+.*aged_out\s+enable.*$/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'data_driven_learning'}->{'aged_out'}->{'state'} = 'enable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'data_driven_learning'}->{'aged_out'}->{'state'} = 'disable';
        }

        if ( grep {/^\s*config\s+igmp_snooping\s+(?:vlan_name|vlanid)\s+(?:$PORTS|default|iptv)\s+.*fast_leave\s+disable.*$/} @grep_igmp_snooping ) {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'fast_leave'}->{'state'} = 'disable';
        }
        else {
            ${$hashref}->{'iptv'}->{'igmp_snooping'}->{'fast_leave'}->{'state'} = 'enable';
        }
    }
    return 1;
}

sub LLDP {1}
sub l2pt{1}
sub DHCP{
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;
    my $configstr = join "\n", @$configref;

    if (my @grep_dhcp_trigger = grep {/^\s*enable\s+dhcp_local_relay\s*$/} @str ) {
        ${$hashref}->{'dhcp'}->{'dhcp_local_relay'} = 'enable';
    } else {
        ${$hashref}->{'dhcp'}->{'dhcp_local_relay'} = 'disable';
    }

    if (my @grep_dhcp_option_82 = grep {/^\s*config\s+dhcp_local_relay\s+option_82\s+remote_id\s+default\s*$/} @str ) {
        ${$hashref}->{'dhcp'}->{'option_82_remote_id_default'} = 'enable';
    } else {
        ${$hashref}->{'dhcp'}->{'option_82_remote_id_default'} = 'disable';
    }

    my @ports_all = keys %{${$hashref}->{port}};
    foreach my $port ( @ports_all ) {
        ${$hashref}->{port}->{$port}->{'dhcp'}->{'filter_dhcp_server'} = 'disable';
        ${$hashref}->{port}->{$port}->{'dhcp'}->{'option_82_replace'} = 'disable';
        ${$hashref}->{port}->{$port}->{'dhcp'}->{'dhcp_local_relay'} = 'disable';
    }


    if ( my @grep = grep {/^\s*config\s+filter\s+dhcp_server\s+ports\s+($PORTS)\s+state\s+enable\s*$/} @str ) {
        foreach my $str ( @grep ) {
            $str =~ /^\s*config\s+filter\s+dhcp_server\s+ports\s+($PORTS)\s+state\s+enable\s*$/;
            my @ports = ParsePorts($1);
            foreach my $port ( @ports ) {
                ${$hashref}->{port}->{$port}->{'dhcp'}->{'filter_dhcp_server'} = 'enable';
            }
        }
    }

    if ( my @grep = grep {/^\s*config\s+dhcp_local_relay\s+option_82\s+ports\s+($PORTS)\s+policy\s+replace\s*$/} @str ) {
        foreach my $str ( @grep ) {
            $str =~ /^\s*config\s+dhcp_local_relay\s+option_82\s+ports\s+($PORTS)\s+policy\s+replace\s*$/;
            my @ports = ParsePorts($1);
            foreach my $port ( @ports ) {
                ${$hashref}->{port}->{$port}->{'dhcp'}->{'option_82_replace'} = 'enable';
            }
        }
    }

    if ( my @grep = grep {/^\s*config\s+dhcp_local_relay\s+port\s+($PORTS)\s+state\s+enable\s*$/} @str ) {
        foreach my $str ( @grep ) {
            $str =~ /^\s*config\s+dhcp_local_relay\s+port\s+($PORTS)\s+state\s+enable\s*$/;
            my @ports = ParsePorts($1);
            foreach my $port ( @ports ) {
                ${$hashref}->{port}->{$port}->{'dhcp'}->{'dhcp_local_relay'} = 'enable';
            }
        }
    }


    my @pcv_untagged;
    my @pcv_tagged;
    my @pcv_dhcp;
    my @pcv_ex;
    my @exclude_vlans;
    my %vlans_ports_bad;
    my %vlans_ports_good;

    foreach my $conf_vlan ( grep {/^\s*config\s+(?:gvrp|port_vlan)\s+($PORTS).*pvid\s+(\d{2,5}).*$/} @str) {
        $conf_vlan =~ m/^\s*config\s+(?:gvrp|port_vlan)\s+($PORTS).*pvid\s+(\d{2,5}).*$/;
        my $vlan = $2;
        my @ports = ParsePorts($1);
        my $access_flag = 1;
        foreach my $port ( @ports ) {
            if (${$hashref}->{port}->{$port}->{role} =~ /(common|PA_RADIO)/ or ! defined  ${$hashref}->{port}->{$port}->{role}){
                push @pcv_ex, $vlan;
            }
            elsif (!(${$hashref}->{port}->{$port}->{role} =~ /(PA_CLNT|PM_NOCTL|PA_PPPOE)/)) {
                $access_flag = 0;
                push @{ $vlans_ports_bad{$vlan} }, $port;
                push @pcv_tagged, $vlan;
                #      } elsif (${$hashref}->{port}->{$port}->{role} =~ /PA_RADIO/) {
                #        push @exclude_vlans, $vlan;
            } else {
                push @{ $vlans_ports_good{$vlan} }, $port;
                push @pcv_untagged, $vlan;
            }
        }
        #    if ( $access_flag ){
        #      push @pcv_untagged, $vlan;
        #    }
    }

    foreach my $conf_vlan ( grep {/^\s*config\s+dhcp_local_relay\s+vlan\s+(vlanid\s)?(.*)\s+state\s+enable\s*$/} @str) {
        $conf_vlan =~ m/^\s*config\s+dhcp_local_relay\s+vlan\s+(vlanid\s)?(.*)\s+state\s+enable\s*$/;
        my @vlans = ParseVlanStr ($2);
        foreach my $vlan (@vlans){
            push @pcv_dhcp, $vlan;
        }
    }

    my %pcv_hash;
    foreach my $vlan (@pcv_untagged){
        $pcv_hash{$vlan} = 1;
    }

    foreach my $vlan (@pcv_dhcp){
        if ( exists $pcv_hash{$vlan} or (grep {/^$vlan$/} @pcv_ex and ! grep {/^$vlan$/} @pcv_tagged)) {
            #    if ( exists $pcv_hash{$vlan}){
            $pcv_hash{$vlan} = 0;
        } else {
            $pcv_hash{$vlan} = 1;
        }
    }

    foreach my $vlan (@exclude_vlans){
        $pcv_hash{$vlan} = 0;
    }

    my $pcv_untagged_str = join(", ", @pcv_untagged);
    my $pcv_dhcp_str = join(", ", @pcv_dhcp);

    my @keys = keys %pcv_hash;
    my $error = '';
    my @dhcp_err;
    my @pcv_err;
    my @vlan_err;
    foreach my $key (@keys){
        if (exists $vlans_ports_good{$key} and exists $vlans_ports_bad{$key} ){
            my $ports = 'On: ' . join(", ", @{$vlans_ports_good{$key}}) . '; Off: ' . join(", ", @{$vlans_ports_bad{$key}});
            push @vlan_err, "$key($ports)";
            next;
        }
        if (  $pcv_hash{$key} ){
            my $ports = '-';
            if (grep {/^$key$/} @pcv_dhcp){
                $ports = join(", ", @{$vlans_ports_bad{$key}}) if (exists $vlans_ports_bad{$key});
                push @dhcp_err, "$key($ports)";
            } else {
                $ports = join(", ", @{$vlans_ports_good{$key}}) if (exists $vlans_ports_good{$key});
                push @pcv_err, "$key($ports)";
            }
            #      $error = $error . "$key($ports) ";
        }
    }

    if (@vlan_err){
        $error = $error . 'Should be both enabled and disabled(!!!): ' . join(', ', @vlan_err) . '. ';
    }
    if (@pcv_err){
        $error = $error . 'Should be enabled: ' . join(', ', @pcv_err) . '. ';
    }
    if (@dhcp_err){
        $error = $error . 'Should be disabled: ' . join(', ', @dhcp_err) . '. ';
    }

    if ( $error ){
        ${$hashref}->{'dhcp'}->{'pcv'} = $error;
    } else {
        ${$hashref}->{'dhcp'}->{'pcv'} = 'correct';
    }


    return 1;

}

sub Common{
    my $mod = shift;

    my $hashref = shift;
    my $configref = shift;
    my @str = @$configref;
    my $configstr = join "\n", @$configref;
    # print("ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ");
    ${$hashref}->{'common'}->{'HOSTNAME'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'SYSLOC'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'SYSCONT'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'MGMT_VLAN'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'MGMT_MASK'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'GW'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'TZ'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'SYSLOG_IP'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'MCAST_VLAN'} = 'UNDEFINED';
    ${$hashref}->{'common'}->{'STP_PRIO'} = 'UNDEFINED';

    my %param_hash = (
        'HOSTNAME'          => '\n\s*config command_prompt (.*?)\s*\n',
        'SYSLOC'            => '\n\s*config snmp system_location (.*?)\s*\n',
        'SYSCONT'           => '\n\s*config snmp system_contact (.*?)\s*\n',
        'GW'                => '\n\s*create iproute default (\S+) (?:\d+)(?: primary)?\s*\n',
        'NTP1_IP'           => '\n\s*config s?ntp primary (\S+)',
        'NTP2_IP'           => '\n\s*config s?ntp primary (?:\S+) secondary (\S+) .*\s*\n',
        'TZ'                => '\n\s*config time_zone operator \+ hour (\d+)',

        #    'RADIUS1_IP'        => '\n\s*radius-server authentication (\S+) 2030 weight 100\s*\n',
        #    'RADIUS2_IP'        => '\n\s*radius-server authentication (\S+) 2030 weight 90\s*\n',

        'MCAST_VLAN'        => '\n\s*create igmp_snooping multicast_vlan\s+(?:\S+)\s+(\d+)\s*\n',
        'STP_PRIO'          => '\n\s*config stp priority (\d+) instance_id 0\s*\n'
    );


    foreach my $param (keys %param_hash){
        my $re = $param_hash{$param};
        my $regex = qr/$re/i;

        if (my $match = $configstr =~ /$regex/ms) {
            ${$hashref}->{'common'}->{$param} = $1;
        }
    }

    if (${$hashref}->{'common'}->{'TZ'} < 10){
        ${$hashref}->{'common'}->{'TZ'} = '0' . ${$hashref}->{'common'}->{'TZ'};
    }

    if (${$hashref}->{'common'}->{'HOSTNAME'} eq 'default' or ${$hashref}->{'common'}->{'HOSTNAME'} eq 'UNDEFINED'){
        if (my $match = $configstr =~ /\n\s*config snmp system_name (.*?)\s*\n/ms) {
            ${$hashref}->{'common'}->{'HOSTNAME'} = $1;
        }
    }
    my $vlan_num;
    my $mgmt_ip = ${$hashref}->{'common'}->{'MGMT_IP'};
    while (my $match = $configstr =~ /\n\s*config ipif System vlan (.*?) ipaddress (\S+)\/(\d+) state enable/gms) {
        $vlan_num = $1;
        my $ip = $2;
        my $netbit = $3;

        if ($ip eq $mgmt_ip){
            my $_bit = ( 2 ** (32 - $netbit) ) - 1;
            my ($full_mask)  = unpack( "N", pack( "C4", 255,255,255,255 ) );
            my $mask = join( '.', unpack( "C4", pack( "N", ( $full_mask ^ $_bit ) ) ) );
            ${$hashref}->{'common'}->{'MGMT_VLAN'} = $vlan_num;
            ${$hashref}->{'common'}->{'MGMT_MASK'} = $mask;
            last;
        }
    }
    #   print("xxxxxxxxxxxxxxxxxxxxxx");

    #  print Dumper(${$hashref}->{'common'}->{'MGMT_VLAN'});
    if (${$hashref}->{'common'}->{'MGMT_VLAN'} eq 'UNDEFINED'){
        while (my $match = $configstr =~ /\n\s*config ipif (\S+) ipaddress (\S+)\/(\S+)/gms) {
            my $ifname = $1;
            my $ip = $2;
            my $mask = $3;

            if ($ip eq $mgmt_ip){
                if ($mask !~ /\d+\.\d+/){
                    my $_bit = ( 2 ** (32 - $mask) ) - 1;
                    my ($full_mask)  = unpack( "N", pack( "C4", 255,255,255,255 ) );
                    $mask = join( '.', unpack( "C4", pack( "N", ( $full_mask ^ $_bit ) ) ) );
                }

                if ($configstr =~ /^\s?+config ipif $ifname vlan (.*?)$/m){
                    $vlan_num = $1;
                    ${$hashref}->{'common'}->{'MGMT_VLAN'} = $vlan_num;
                    ${$hashref}->{'common'}->{'MGMT_MASK'} = $mask;
                }
                if (${$hashref}->{'common'}->{'MGMT_VLAN'} eq 'UNDEFINED'){
                    $configstr =~ /^\s?+config ipif $ifname ipaddress \S+\/\S+ vlan (.*?)$/m;
                    $vlan_num = $1;

                }
            }
        }
    }
    #config ipif System ipaddress 10.242.199.2/24 vlan qnqmng

    my $temp = $configstr;

    $temp =~ /^create vlan $vlan_num tag (\d+).*?$/gm;#) {

    ${$hashref}->{'common'}->{'MGMT_VLAN'} = $1;
    $temp = "";



    ${$hashref}->{'common'}->{'SYSLOG_IP'} = ${$hashref}->{'common'}->{'EQM_IP'};#


    ${$hashref}->{'common_acl'}->{'109.194.154.0'} = '255.255.255.224';
    ${$hashref}->{'common_acl'}->{'212.33.233.40'} = '255.255.255.248';
    ${$hashref}->{'common_acl'}->{'10.2.1.0'} = '255.255.255.0';
    ${$hashref}->{'common_acl'}->{${$hashref}->{'common'}->{'EQM_IP'}} = '255.255.255.255';
    ${$hashref}->{'common_acl'}->{${$hashref}->{'common'}->{'GW'}} = '255.255.255.255';

    foreach my $grep (grep {/create trusted_host (\S*)/} @str){
        $grep =~ /create trusted_host ([\d.]+)/;
        ${$hashref}->{'common_acl'}->{$1} = '255.255.255.255';
    }

    foreach my $grep (grep {/create trusted_host network (\S+)\/(\S+)/} @str){
        $grep =~ /create trusted_host network (\S+)\/(\S+)/;
        my $ip = $1;
        my $mask = $2;

        if ($mask !~ /\d+\.\d+/){
            my $_bit = ( 2 ** (32 - $mask) ) - 1;
            my ($full_mask)  = unpack( "N", pack( "C4", 255,255,255,255 ) );
            $mask = join( '.', unpack( "C4", pack( "N", ( $full_mask ^ $_bit ) ) ) );
        }

        ${$hashref}->{'common_acl'}->{$ip} = $mask;
    }
}

sub DigitalCountry{1}

1;
