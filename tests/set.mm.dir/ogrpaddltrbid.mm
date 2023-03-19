include "wbr.mm"
include "co.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "coppg.mm"
include "cfv.mm"
include "cogrp.mm"
include "simpr.mm"
include "ogrpaddltrd.mm"
include "cminusg.mm"
include "cgrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "w3a.mm"
include "cplusg.mm"
include "eqid.mm"
include "oppgplus.mm"
include "oppgbas.mm"
include "grpcl.mm"
include "syl5eqelr.mm"
include "syl3anc.mm"
include "oppggrpb.mm"
include "sylibr.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "c0g.mm"
include "wceq.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "3brtr3d.mm"
include "impbida.mm"

theorem ogrpaddltrbid
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ogrpaddlt.0: |- B = ( Base ` G )
  assume ogrpaddlt.1: |- .< = ( lt ` G )
  assume ogrpaddlt.2: |- .+ = ( +g ` G )
  assume ogrpaddltrd.1: |- ( ph -> G e. V )
  assume ogrpaddltrd.2: |- ( ph -> ( oppG ` G ) e. oGrp )
  assume ogrpaddltrd.3: |- ( ph -> X e. B )
  assume ogrpaddltrd.4: |- ( ph -> Y e. B )
  assume ogrpaddltrd.5: |- ( ph -> Z e. B )


  assert |- ( ph -> ( X .< Y <-> ( Z .+ X ) .< ( Z .+ Y ) ) )

  proof
    wph
    cX
    cY
    c.lt
    wbr
    #
    cZ
    cX
    c.pl
    co
    #
    cZ
    cY
    c.pl
    co
    #
    c.lt
    wbr
    #
    wph
    @0
    wa
    cB
    c.pl
    c.lt
    cG
    cV
    cX
    cY
    cZ
    ogrpaddlt.0
    ogrpaddlt.1
    ogrpaddlt.2
    wph
    cG
    cV
    wcel
    #
    @0
    ogrpaddltrd.1
    adantr
    wph
    cG
    coppg
    cfv
    #
    cogrp
    wcel
    #
    @0
    ogrpaddltrd.2
    adantr
    wph
    cX
    cB
    wcel
    #
    @0
    ogrpaddltrd.3
    adantr
    wph
    cY
    cB
    wcel
    #
    @0
    ogrpaddltrd.4
    adantr
    wph
    cZ
    cB
    wcel
    #
    @0
    ogrpaddltrd.5
    adantr
    wph
    @0
    simpr
    ogrpaddltrd
    wph
    @3
    wa
    #
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    @1
    c.pl
    co
    #
    @12
    @2
    c.pl
    co
    #
    cX
    cY
    c.lt
    @10
    cB
    c.pl
    c.lt
    cG
    cV
    @1
    @2
    @12
    ogrpaddlt.0
    ogrpaddlt.1
    ogrpaddlt.2
    wph
    @4
    @3
    ogrpaddltrd.1
    adantr
    wph
    @6
    @3
    ogrpaddltrd.2
    adantr
    @10
    @5
    cgrp
    wcel
    #
    @7
    @9
    @1
    cB
    wcel
    wph
    @15
    @3
    wph
    @6
    @15
    ogrpaddltrd.2
    @5
    ogrpgrp
    syl
    adantr
    #
    wph
    @7
    @3
    ogrpaddltrd.3
    adantr
    #
    wph
    @9
    @3
    ogrpaddltrd.5
    adantr
    #
    @15
    @7
    @9
    w3a
    @1
    cX
    cZ
    @5
    cplusg
    cfv
    #
    co
    cB
    c.pl
    @19
    cG
    @5
    cX
    cZ
    ogrpaddlt.2
    @5
    eqid
    #
    @19
    eqid
    #
    oppgplus
    cB
    @19
    @5
    cX
    cZ
    cB
    cG
    @5
    @20
    ogrpaddlt.0
    oppgbas
    #
    @21
    grpcl
    syl5eqelr
    syl3anc
    @10
    @15
    @8
    @9
    @2
    cB
    wcel
    @16
    wph
    @8
    @3
    ogrpaddltrd.4
    adantr
    #
    @18
    @15
    @8
    @9
    w3a
    @2
    cY
    cZ
    @19
    co
    cB
    c.pl
    @19
    cG
    @5
    cY
    cZ
    ogrpaddlt.2
    @20
    @21
    oppgplus
    cB
    @19
    @5
    cY
    cZ
    @22
    @21
    grpcl
    syl5eqelr
    syl3anc
    @10
    cG
    cgrp
    wcel
    #
    @9
    @12
    cB
    wcel
    #
    @10
    @15
    @24
    @16
    cG
    @5
    @20
    oppggrpb
    sylibr
    #
    @18
    cB
    cG
    @11
    cZ
    ogrpaddlt.0
    @11
    eqid
    #
    grpinvcl
    syl2anc
    #
    wph
    @3
    simpr
    ogrpaddltrd
    @10
    @12
    cZ
    c.pl
    co
    #
    cX
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    cX
    c.pl
    co
    #
    @13
    cX
    @10
    @29
    @31
    cX
    c.pl
    @10
    @24
    @9
    @29
    @31
    wceq
    @26
    @18
    cB
    c.pl
    cG
    @11
    cZ
    @31
    ogrpaddlt.0
    ogrpaddlt.2
    @31
    eqid
    #
    @27
    grplinv
    syl2anc
    #
    oveq1d
    @10
    @24
    @25
    @9
    @7
    @30
    @13
    wceq
    @26
    @28
    @18
    @17
    cB
    c.pl
    cG
    @12
    cZ
    cX
    ogrpaddlt.0
    ogrpaddlt.2
    grpass
    syl13anc
    @10
    @24
    @7
    @32
    cX
    wceq
    @26
    @17
    cB
    c.pl
    cG
    cX
    @31
    ogrpaddlt.0
    ogrpaddlt.2
    @33
    grplid
    syl2anc
    3eqtr3d
    @10
    @29
    cY
    c.pl
    co
    #
    @31
    cY
    c.pl
    co
    #
    @14
    cY
    @10
    @29
    @31
    cY
    c.pl
    @34
    oveq1d
    @10
    @24
    @25
    @9
    @8
    @35
    @14
    wceq
    @26
    @28
    @18
    @23
    cB
    c.pl
    cG
    @12
    cZ
    cY
    ogrpaddlt.0
    ogrpaddlt.2
    grpass
    syl13anc
    @10
    @24
    @8
    @36
    cY
    wceq
    @26
    @23
    cB
    c.pl
    cG
    cY
    @31
    ogrpaddlt.0
    ogrpaddlt.2
    @33
    grplid
    syl2anc
    3eqtr3d
    3brtr3d
    impbida
end
