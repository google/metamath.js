include "cv.mm"
include "co.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cn0.mm"
include "wcel.mm"
include "simplr.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "csg.mm"
include "cfv.mm"
include "cplusg.mm"
include "ad2antrr.mm"
include "mulg1.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "cz.mm"
include "cogrp.mm"
include "ogrpgrp.mm"
include "1zzd.mm"
include "nn0zd.mm"
include "eqid.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "cpo.mm"
include "comnd.mm"
include "ctos.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "tospos.mm"
include "3syl.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "peano2zd.mm"
include "simprr.mm"
include "ogrpsub.mm"
include "syl131anc.mm"
include "cmin.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncan2d.mm"
include "mulgsubdir.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "wi.mm"
include "wral.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "simprl.mm"
include "ogrpsublt.mm"
include "eqbrtrrd.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "w3a.mm"
include "posasymb.mm"
include "biimpa.mm"
include "syl32anc.mm"
include "3eqtr4rd.mm"
include "grpnpcan.mm"
include "addcomd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "archirng.mm"
include "r19.29a.mm"

theorem archiabllem1a
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let cU: class U
  let vn: setvar n
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
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
  assume archiabllem1a.x: |- ( ph -> X e. B )
  assume archiabllem1a.c: |- ( ph -> .0. .< X )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint U n
  disjoint U x
  disjoint W n
  disjoint W x
  disjoint X n
  disjoint X x
  disjoint n ph
  disjoint ph x
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
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint U m
  disjoint W m
  disjoint W y
  disjoint W z
  disjoint X m
  disjoint m ph
  disjoint ph y
  disjoint ph z
  disjoint .x. m
  disjoint .0. m
  disjoint .< m
  disjoint .<_ m
  assert |- ( ph -> E. n e. NN X = ( n .x. U ) )

  proof
    wph
    vm
    cv
    #
    cU
    c.x
    co
    #
    cX
    c.lt
    wbr
    #
    cX
    @0
    c1
    caddc
    co
    #
    cU
    c.x
    co
    #
    c.le
    wbr
    #
    wa
    #
    cX
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
    cn
    wrex
    #
    vm
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @6
    wa
    #
    @3
    cn
    wcel
    #
    cX
    @4
    wceq
    #
    @10
    @13
    @11
    @14
    wph
    @11
    @6
    simplr
    #
    @0
    nn0p1nn
    syl
    @13
    cX
    @1
    cW
    csg
    cfv
    #
    co
    #
    @1
    cW
    cplusg
    cfv
    #
    co
    #
    c1
    @0
    caddc
    co
    #
    cU
    c.x
    co
    #
    cX
    @4
    @13
    c1
    cU
    c.x
    co
    #
    @1
    @19
    co
    #
    cU
    @1
    @19
    co
    @22
    @20
    @13
    @23
    cU
    @1
    @19
    @13
    cU
    cB
    wcel
    #
    @23
    cU
    wceq
    wph
    @25
    @11
    @6
    archiabllem1.u
    ad2antrr
    #
    cB
    c.x
    cW
    cU
    archiabllem.b
    archiabllem.m
    mulg1
    syl
    #
    oveq1d
    @13
    cW
    cgrp
    wcel
    #
    c1
    cz
    wcel
    @0
    cz
    wcel
    #
    @25
    @22
    @24
    wceq
    @13
    cW
    cogrp
    wcel
    #
    @28
    wph
    @30
    @11
    @6
    archiabllem.g
    ad2antrr
    #
    cW
    ogrpgrp
    syl
    #
    @13
    1zzd
    @13
    @0
    @16
    nn0zd
    #
    @26
    cB
    @19
    c.x
    cW
    c1
    @0
    cU
    archiabllem.b
    archiabllem.m
    @19
    eqid
    #
    mulgdir
    syl13anc
    @13
    @18
    cU
    @1
    @19
    @13
    cW
    cpo
    wcel
    #
    @18
    cB
    wcel
    #
    @25
    @18
    cU
    c.le
    wbr
    #
    cU
    @18
    c.le
    wbr
    #
    @18
    cU
    wceq
    #
    @13
    @30
    @35
    @31
    @30
    cW
    comnd
    wcel
    #
    cW
    ctos
    wcel
    @35
    @30
    @28
    @40
    cW
    isogrp
    simprbi
    cW
    omndtos
    cW
    tospos
    3syl
    syl
    @13
    @28
    cX
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @36
    @32
    wph
    @41
    @11
    @6
    archiabllem1a.x
    ad2antrr
    #
    @13
    @28
    @29
    @25
    @42
    @32
    @33
    @26
    cB
    c.x
    cW
    @0
    cU
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    cB
    cW
    @17
    cX
    @1
    archiabllem.b
    @17
    eqid
    #
    grpsubcl
    syl3anc
    #
    @26
    @13
    @18
    @4
    @1
    @17
    co
    #
    cU
    c.le
    @13
    @30
    @41
    @4
    cB
    wcel
    #
    @42
    @5
    @18
    @47
    c.le
    wbr
    @31
    @43
    @13
    @28
    @3
    cz
    wcel
    #
    @25
    @48
    @32
    @13
    @0
    @33
    peano2zd
    #
    @26
    cB
    c.x
    cW
    @3
    cU
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    @44
    @12
    @2
    @5
    simprr
    cB
    cW
    c.le
    @17
    cX
    @4
    @1
    archiabllem.b
    archiabllem.e
    @45
    ogrpsub
    syl131anc
    @13
    @3
    @0
    cmin
    co
    #
    cU
    c.x
    co
    #
    @23
    @47
    cU
    @13
    @51
    c1
    cU
    c.x
    @13
    @0
    c1
    @13
    @0
    @16
    nn0cnd
    #
    @13
    1cnd
    #
    pncan2d
    oveq1d
    @13
    @28
    @49
    @29
    @25
    @52
    @47
    wceq
    @32
    @50
    @33
    @26
    cB
    c.x
    cW
    @3
    @17
    @0
    cU
    archiabllem.b
    archiabllem.m
    @45
    mulgsubdir
    syl13anc
    @27
    3eqtr3d
    breqtrd
    @13
    @36
    c.0
    vx
    cv
    #
    c.lt
    wbr
    #
    cU
    @55
    c.le
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    c.0
    @18
    c.lt
    wbr
    #
    @38
    @46
    wph
    @59
    @11
    @6
    wph
    @58
    vx
    cB
    wph
    @55
    cB
    wcel
    @56
    @57
    archiabllem1.s
    3expia
    ralrimiva
    ad2antrr
    @13
    @1
    @1
    @17
    co
    #
    c.0
    @18
    c.lt
    @13
    @28
    @42
    @61
    c.0
    wceq
    @32
    @44
    cB
    cW
    @17
    @1
    c.0
    archiabllem.b
    archiabllem.0
    @45
    grpsubid
    syl2anc
    @13
    @30
    @42
    @41
    @42
    @2
    @61
    @18
    c.lt
    wbr
    @31
    @44
    @43
    @44
    @12
    @2
    @5
    simprl
    cB
    c.lt
    cW
    @17
    @1
    cX
    @1
    archiabllem.b
    archiabllem.t
    @45
    ogrpsublt
    syl131anc
    eqbrtrrd
    @58
    @60
    @38
    wi
    vx
    @18
    cB
    @55
    @18
    wceq
    @56
    @60
    @57
    @38
    @55
    @18
    c.0
    c.lt
    breq2
    @55
    @18
    cU
    c.le
    breq2
    imbi12d
    rspcv
    syl3c
    @35
    @36
    @25
    w3a
    @37
    @38
    wa
    @39
    cB
    cW
    c.le
    @18
    cU
    archiabllem.b
    archiabllem.e
    posasymb
    biimpa
    syl32anc
    oveq1d
    3eqtr4rd
    @13
    @28
    @41
    @42
    @20
    cX
    wceq
    @32
    @43
    @44
    cB
    @19
    cW
    @17
    cX
    @1
    archiabllem.b
    @34
    @45
    grpnpcan
    syl3anc
    @13
    @21
    @3
    cU
    c.x
    @13
    c1
    @0
    @54
    @53
    addcomd
    oveq1d
    3eqtr3d
    @9
    @15
    vn
    @3
    cn
    @7
    @3
    wceq
    @8
    @4
    cX
    @7
    @3
    cU
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    wph
    cB
    c.lt
    c.x
    vm
    c.le
    cW
    cU
    cX
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.t
    archiabllem.e
    archiabllem.m
    archiabllem.g
    archiabllem.a
    archiabllem1.u
    archiabllem1a.x
    archiabllem1.p
    archiabllem1a.c
    archirng
    r19.29a
end
