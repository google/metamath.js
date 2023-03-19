include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wrex.mm"
include "wcel.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simpr.mm"
include "wceq.mm"
include "breq2.mm"
include "id.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "csg.mm"
include "cfv.mm"
include "cgrp.mm"
include "cogrp.mm"
include "simplll.mm"
include "ogrpgrp.mm"
include "3syl.mm"
include "syl.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "ogrpsublt.mm"
include "syl131anc.mm"
include "eqbrtrrd.mm"
include "coppg.mm"
include "grpcl.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "ogrpaddltrd.mm"
include "grpnpcan.mm"
include "cvv.mm"
include "wi.mm"
include "ovexd.mm"
include "pltle.mm"
include "mpd.mm"
include "ctos.mm"
include "wo.mm"
include "comnd.mm"
include "ad2antrr.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "simplr.mm"
include "tlt2.mm"
include "mpjaodan.mm"
include "wral.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "r19.29a.mm"

theorem archiabllem2a
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let c.x: class .x.
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  assume archiabllem.b: |- B = ( Base ` W )
  assume archiabllem.0: |- .0. = ( 0g ` W )
  assume archiabllem.e: |- .<_ = ( le ` W )
  assume archiabllem.t: |- .< = ( lt ` W )
  assume archiabllem.m: |- .x. = ( .g ` W )
  assume archiabllem.g: |- ( ph -> W e. oGrp )
  assume archiabllem.a: |- ( ph -> W e. Archi )
  assume archiabllem2.1: |- .+ = ( +g ` W )
  assume archiabllem2.2: |- ( ph -> ( oppG ` W ) e. oGrp )
  assume archiabllem2.3: |- ( ( ph /\ a e. B /\ .0. .< a ) -> E. b e. B ( .0. .< b /\ b .< a ) )
  assume archiabllem2a.4: |- ( ph -> X e. B )
  assume archiabllem2a.5: |- ( ph -> .0. .< X )

  disjoint a b
  disjoint a c
  disjoint B a
  disjoint b c
  disjoint B b
  disjoint B c
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint a ph
  disjoint b ph
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .< a
  disjoint .< b
  disjoint .< c
  disjoint .0. a
  disjoint .0. b
  disjoint .0. c
  disjoint a b
  disjoint m n
  disjoint m t
  disjoint n t
  disjoint a t
  disjoint b t
  disjoint c t
  disjoint B t
  disjoint W t
  disjoint X t
  disjoint a m
  disjoint a n
  disjoint Y a
  disjoint b m
  disjoint b n
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y t
  disjoint ph t
  disjoint c m
  disjoint c n
  disjoint .+ t
  disjoint .+ m
  disjoint .+ n
  disjoint .<_ t
  disjoint .<_ m
  disjoint .<_ n
  disjoint .< t
  disjoint .< m
  disjoint .< n
  disjoint .0. t
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint U m
  disjoint U n
  disjoint U x
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint .0. m
  disjoint .0. n
  disjoint .0. x
  disjoint .< m
  disjoint .< n
  disjoint .< x
  disjoint .<_ m
  disjoint .<_ x
  assert |- ( ph -> E. c e. B ( .0. .< c /\ ( c .+ c ) .<_ X ) )

  proof
    wph
    c.0
    vb
    cv
    #
    c.lt
    wbr
    #
    @0
    cX
    c.lt
    wbr
    #
    wa
    #
    c.0
    vc
    cv
    #
    c.lt
    wbr
    #
    @4
    @4
    c.pl
    co
    #
    cX
    c.le
    wbr
    #
    wa
    #
    vc
    cB
    wrex
    #
    vb
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @3
    wa
    #
    @0
    @0
    c.pl
    co
    #
    cX
    c.le
    wbr
    #
    @9
    cX
    @13
    c.lt
    wbr
    #
    @12
    @14
    wa
    @10
    @1
    @14
    @9
    wph
    @10
    @3
    @14
    simpllr
    @11
    @1
    @2
    @14
    simplrl
    @12
    @14
    simpr
    @8
    @1
    @14
    wa
    vc
    @0
    cB
    @4
    @0
    wceq
    #
    @5
    @1
    @7
    @14
    @4
    @0
    c.0
    c.lt
    breq2
    @16
    @6
    @13
    cX
    c.le
    @16
    @4
    @0
    @4
    @0
    c.pl
    @16
    id
    #
    @17
    oveq12d
    breq1d
    anbi12d
    rspcev
    syl12anc
    @12
    @15
    wa
    #
    cX
    @0
    cW
    csg
    cfv
    #
    co
    #
    cB
    wcel
    #
    c.0
    @20
    c.lt
    wbr
    #
    @20
    @20
    c.pl
    co
    #
    cX
    c.le
    wbr
    #
    @9
    @18
    cW
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    @10
    @21
    @18
    wph
    cW
    cogrp
    wcel
    #
    @25
    wph
    @10
    @3
    @15
    simplll
    #
    archiabllem.g
    cW
    ogrpgrp
    #
    3syl
    #
    @18
    wph
    @26
    @28
    archiabllem2a.4
    syl
    #
    wph
    @10
    @3
    @15
    simpllr
    #
    cB
    cW
    @19
    cX
    @0
    archiabllem.b
    @19
    eqid
    #
    grpsubcl
    syl3anc
    #
    @18
    @0
    @0
    @19
    co
    #
    c.0
    @20
    c.lt
    @18
    @25
    @10
    @35
    c.0
    wceq
    @30
    @32
    cB
    cW
    @19
    @0
    c.0
    archiabllem.b
    archiabllem.0
    @33
    grpsubid
    syl2anc
    #
    @18
    @27
    @10
    @26
    @10
    @2
    @35
    @20
    c.lt
    wbr
    @18
    wph
    @27
    @28
    archiabllem.g
    syl
    #
    @32
    @31
    @32
    @11
    @1
    @2
    @15
    simplrr
    cB
    c.lt
    cW
    @19
    @0
    cX
    @0
    archiabllem.b
    archiabllem.t
    @33
    ogrpsublt
    syl131anc
    eqbrtrrd
    @18
    @23
    cX
    c.lt
    wbr
    #
    @24
    @18
    @23
    @20
    @0
    c.pl
    co
    #
    cX
    c.lt
    @18
    cB
    c.pl
    c.lt
    cW
    cgrp
    @20
    @0
    @20
    archiabllem.b
    archiabllem.t
    archiabllem2.1
    @30
    @18
    wph
    cW
    coppg
    cfv
    cogrp
    wcel
    @28
    archiabllem2.2
    syl
    @34
    @32
    @34
    @18
    @20
    @13
    @0
    @19
    co
    #
    @0
    c.lt
    @18
    @27
    @26
    @13
    cB
    wcel
    #
    @10
    @15
    @20
    @40
    c.lt
    wbr
    @37
    @31
    @18
    @25
    @10
    @10
    @41
    @30
    @32
    @32
    cB
    c.pl
    cW
    @0
    @0
    archiabllem.b
    archiabllem2.1
    grpcl
    #
    syl3anc
    @32
    @12
    @15
    simpr
    cB
    c.lt
    cW
    @19
    cX
    @13
    @0
    archiabllem.b
    archiabllem.t
    @33
    ogrpsublt
    syl131anc
    @18
    @40
    @0
    @35
    c.pl
    co
    #
    @0
    c.0
    c.pl
    co
    #
    @0
    @18
    @25
    @10
    @10
    @10
    @40
    @43
    wceq
    @30
    @32
    @32
    @32
    cB
    c.pl
    cW
    @19
    @0
    @0
    @0
    archiabllem.b
    archiabllem2.1
    @33
    grpaddsubass
    syl13anc
    @18
    @35
    c.0
    @0
    c.pl
    @36
    oveq2d
    @18
    @25
    @10
    @44
    @0
    wceq
    @30
    @32
    cB
    c.pl
    cW
    @0
    c.0
    archiabllem.b
    archiabllem2.1
    archiabllem.0
    grprid
    syl2anc
    3eqtrd
    breqtrd
    ogrpaddltrd
    @18
    @25
    @26
    @10
    @39
    cX
    wceq
    @30
    @31
    @32
    cB
    c.pl
    cW
    @19
    cX
    @0
    archiabllem.b
    archiabllem2.1
    @33
    grpnpcan
    syl3anc
    breqtrd
    @18
    @25
    @23
    cvv
    wcel
    @26
    @38
    @24
    wi
    @30
    @18
    @20
    @20
    c.pl
    ovexd
    @31
    cgrp
    cvv
    cB
    c.lt
    cW
    c.le
    @23
    cX
    archiabllem.e
    archiabllem.t
    pltle
    syl3anc
    mpd
    @8
    @22
    @24
    wa
    vc
    @20
    cB
    @4
    @20
    wceq
    #
    @5
    @22
    @7
    @24
    @4
    @20
    c.0
    c.lt
    breq2
    @45
    @6
    @23
    cX
    c.le
    @45
    @4
    @20
    @4
    @20
    c.pl
    @45
    id
    #
    @46
    oveq12d
    breq1d
    anbi12d
    rspcev
    syl12anc
    @12
    cW
    ctos
    wcel
    #
    @41
    @26
    @14
    @15
    wo
    @12
    @27
    cW
    comnd
    wcel
    #
    @47
    wph
    @27
    @10
    @3
    archiabllem.g
    ad2antrr
    #
    @27
    @25
    @48
    cW
    isogrp
    simprbi
    cW
    omndtos
    3syl
    @12
    @25
    @10
    @10
    @41
    @12
    @27
    @25
    @49
    @29
    syl
    wph
    @10
    @3
    simplr
    #
    @50
    @42
    syl3anc
    wph
    @26
    @10
    @3
    archiabllem2a.4
    ad2antrr
    cB
    c.lt
    cW
    c.le
    @13
    cX
    archiabllem.b
    archiabllem.e
    archiabllem.t
    tlt2
    syl3anc
    mpjaodan
    wph
    @26
    c.0
    va
    cv
    #
    c.lt
    wbr
    #
    @1
    @0
    @51
    c.lt
    wbr
    #
    wa
    #
    vb
    cB
    wrex
    #
    wi
    #
    va
    cB
    wral
    c.0
    cX
    c.lt
    wbr
    #
    @3
    vb
    cB
    wrex
    #
    archiabllem2a.4
    wph
    @56
    va
    cB
    wph
    @51
    cB
    wcel
    @52
    @55
    archiabllem2.3
    3expia
    ralrimiva
    archiabllem2a.5
    @56
    @57
    @58
    wi
    va
    cX
    cB
    @51
    cX
    wceq
    #
    @52
    @57
    @55
    @58
    @51
    cX
    c.0
    c.lt
    breq2
    @59
    @54
    @3
    vb
    cB
    @59
    @53
    @2
    @1
    @51
    cX
    @0
    c.lt
    breq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl3c
    r19.29a
end
