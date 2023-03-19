include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "co.mm"
include "cz.mm"
include "wrex.mm"
include "wbr.mm"
include "cc0.mm"
include "0zd.mm"
include "simpr.mm"
include "mulg0.mm"
include "syl.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "w3a.mm"
include "cminusg.mm"
include "cfv.mm"
include "cn.mm"
include "cneg.mm"
include "simplr.mm"
include "nnzd.mm"
include "znegcld.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "mulgnegnn.mm"
include "fveq2d.mm"
include "cgrp.mm"
include "cogrp.mm"
include "ogrpgrp.mm"
include "simp2.mm"
include "grpinvinv.mm"
include "3eqtr2rd.mm"
include "carchi.mm"
include "simp1.mm"
include "syl3an1.mm"
include "grpinvcl.mm"
include "cplusg.mm"
include "grpidcl.mm"
include "simp3.mm"
include "ogrpaddlt.mm"
include "syl131anc.mm"
include "grprinv.mm"
include "grplid.mm"
include "3brtr3d.mm"
include "archiabllem1a.mm"
include "r19.29a.mm"
include "3expa.mm"
include "wss.mm"
include "nnssz.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "ctos.mm"
include "w3o.mm"
include "comnd.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "3syl.mm"
include "adantr.mm"
include "tlt3.mm"
include "syl3anc.mm"
include "mpjao3dan.mm"

theorem archiabllem1b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let cU: class U
  let vn: setvar n
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vz: setvar z
  let cX: class X
  assume archiabllem.b: |- B = ( Base ` W )
  assume archiabllem.0: |- .0. = ( 0g ` W )
  assume archiabllem.e: |- .<_ = ( le ` W )
  assume archiabllem.t: |- .< = ( lt ` W )
  assume archiabllem.m: |- .x. = ( .g ` W )
  assume archiabllem.g: |- ( ph -> W e. oGrp )
  assume archiabllem.a: |- ( ph -> W e. Archi )
  assume archiabllem1.u: |- ( ph -> U e. B )
  assume archiabllem1.p: |- ( ph -> .0. .< U )
  assume archiabllem1.s: |- ( ( ph /\ x e. B /\ .0. .< x ) -> U .<_ x )

  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint U n
  disjoint U x
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .x. n
  disjoint .x. x
  disjoint .0. n
  disjoint .0. x
  disjoint .< n
  disjoint .< x
  disjoint .<_ x
  disjoint a b
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
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B z
  disjoint U m
  disjoint W m
  disjoint W z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m ph
  disjoint ph z
  disjoint .x. m
  disjoint .0. m
  disjoint .< m
  disjoint .<_ m
  assert |- ( ( ph /\ y e. B ) -> E. n e. ZZ y = ( n .x. U ) )

  proof
    wph
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @0
    c.0
    wceq
    #
    @0
    vn
    cv
    #
    cU
    c.x
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @0
    c.0
    c.lt
    wbr
    #
    c.0
    @0
    c.lt
    wbr
    #
    @2
    @3
    wa
    #
    cc0
    cz
    wcel
    @0
    cc0
    cU
    c.x
    co
    #
    wceq
    #
    @7
    @10
    0zd
    @10
    @0
    c.0
    @11
    @2
    @3
    simpr
    wph
    @11
    c.0
    wceq
    #
    @1
    @3
    wph
    cU
    cB
    wcel
    #
    @13
    archiabllem1.u
    cB
    c.x
    cW
    cU
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.m
    mulg0
    syl
    ad2antrr
    eqtr4d
    @6
    @12
    vn
    cc0
    cz
    @4
    cc0
    wceq
    @5
    @11
    @0
    @4
    cc0
    cU
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @1
    @8
    @7
    wph
    @1
    @8
    w3a
    #
    @0
    cW
    cminusg
    cfv
    #
    cfv
    #
    vm
    cv
    #
    cU
    c.x
    co
    #
    wceq
    #
    @7
    vm
    cn
    @15
    @18
    cn
    wcel
    #
    wa
    #
    @20
    wa
    #
    @18
    cneg
    #
    cz
    wcel
    @0
    @24
    cU
    c.x
    co
    #
    wceq
    #
    @7
    @23
    @18
    @23
    @18
    @15
    @21
    @20
    simplr
    #
    nnzd
    znegcld
    @23
    @25
    @19
    @16
    cfv
    #
    @17
    @16
    cfv
    #
    @0
    @23
    @21
    @14
    @25
    @28
    wceq
    @27
    @15
    @14
    @21
    @20
    wph
    @1
    @14
    @8
    archiabllem1.u
    3ad2ant1
    #
    ad2antrr
    cB
    c.x
    cW
    @16
    @18
    cU
    archiabllem.b
    archiabllem.m
    @16
    eqid
    #
    mulgnegnn
    syl2anc
    @23
    @17
    @19
    @16
    @22
    @20
    simpr
    fveq2d
    @15
    @29
    @0
    wceq
    #
    @21
    @20
    @15
    cW
    cgrp
    wcel
    #
    @1
    @32
    @15
    cW
    cogrp
    wcel
    #
    @33
    wph
    @1
    @34
    @8
    archiabllem.g
    3ad2ant1
    #
    cW
    ogrpgrp
    #
    syl
    #
    wph
    @1
    @8
    simp2
    #
    cB
    cW
    @16
    @0
    archiabllem.b
    @31
    grpinvinv
    syl2anc
    ad2antrr
    3eqtr2rd
    @6
    @26
    vn
    @24
    cz
    @4
    @24
    wceq
    @5
    @25
    @0
    @4
    @24
    cU
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @15
    vx
    cB
    c.lt
    c.x
    cU
    vm
    c.le
    cW
    @17
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    @35
    wph
    @1
    cW
    carchi
    wcel
    #
    @8
    archiabllem.a
    3ad2ant1
    @30
    wph
    @1
    c.0
    cU
    c.lt
    wbr
    #
    @8
    archiabllem1.p
    3ad2ant1
    @15
    wph
    vx
    cv
    #
    cB
    wcel
    #
    c.0
    @41
    c.lt
    wbr
    #
    cU
    @41
    c.le
    wbr
    #
    wph
    @1
    @8
    simp1
    archiabllem1.s
    syl3an1
    @15
    @33
    @1
    @17
    cB
    wcel
    #
    @37
    @38
    cB
    cW
    @16
    @0
    archiabllem.b
    @31
    grpinvcl
    syl2anc
    #
    @15
    @0
    @17
    cW
    cplusg
    cfv
    #
    co
    #
    c.0
    @17
    @47
    co
    #
    c.0
    @17
    c.lt
    @15
    @34
    @1
    c.0
    cB
    wcel
    #
    @45
    @8
    @48
    @49
    c.lt
    wbr
    @35
    @38
    @15
    @33
    @50
    @37
    cB
    cW
    c.0
    archiabllem.b
    archiabllem.0
    grpidcl
    #
    syl
    @46
    wph
    @1
    @8
    simp3
    cB
    @47
    c.lt
    cW
    @0
    c.0
    @17
    archiabllem.b
    archiabllem.t
    @47
    eqid
    #
    ogrpaddlt
    syl131anc
    @15
    @33
    @1
    @48
    c.0
    wceq
    @37
    @38
    cB
    @47
    cW
    @16
    @0
    c.0
    archiabllem.b
    @52
    archiabllem.0
    @31
    grprinv
    syl2anc
    @15
    @33
    @45
    @49
    @17
    wceq
    @37
    @46
    cB
    @47
    cW
    @17
    c.0
    archiabllem.b
    @52
    archiabllem.0
    grplid
    syl2anc
    3brtr3d
    archiabllem1a
    r19.29a
    3expa
    cn
    cz
    wss
    @2
    @9
    wa
    @6
    vn
    cn
    wrex
    #
    @7
    nnssz
    wph
    @1
    @9
    @53
    wph
    @1
    @9
    w3a
    #
    vx
    cB
    c.lt
    c.x
    cU
    vn
    c.le
    cW
    @0
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    wph
    @1
    @34
    @9
    archiabllem.g
    3ad2ant1
    wph
    @1
    @39
    @9
    archiabllem.a
    3ad2ant1
    wph
    @1
    @14
    @9
    archiabllem1.u
    3ad2ant1
    wph
    @1
    @40
    @9
    archiabllem1.p
    3ad2ant1
    @54
    wph
    @42
    @43
    @44
    wph
    @1
    @9
    simp1
    archiabllem1.s
    syl3an1
    wph
    @1
    @9
    simp2
    wph
    @1
    @9
    simp3
    archiabllem1a
    3expa
    @6
    vn
    cn
    cz
    ssrexv
    mpsyl
    @2
    cW
    ctos
    wcel
    #
    @1
    @50
    @3
    @8
    @9
    w3o
    wph
    @55
    @1
    wph
    @34
    cW
    comnd
    wcel
    #
    @55
    archiabllem.g
    @34
    @33
    @56
    cW
    isogrp
    simprbi
    cW
    omndtos
    3syl
    adantr
    wph
    @1
    simpr
    wph
    @50
    @1
    wph
    @34
    @33
    @50
    archiabllem.g
    @36
    @51
    3syl
    adantr
    cB
    c.lt
    cW
    @0
    c.0
    archiabllem.b
    archiabllem.t
    tlt3
    syl3anc
    mpjao3dan
end
