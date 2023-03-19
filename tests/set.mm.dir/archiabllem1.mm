include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cabl.mm"
include "cogrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "wa.mm"
include "cz.mm"
include "caddc.mm"
include "simplr.mm"
include "zcnd.mm"
include "simpr.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "adantllr.mm"
include "adantlr.mm"
include "adantr.mm"
include "simpllr.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "wrex.mm"
include "simplll.mm"
include "simpr1r.mm"
include "3anassrs.mm"
include "archiabllem1b.mm"
include "syl2anc.mm"
include "r19.29a.mm"
include "adantrr.mm"
include "ralrimivva.mm"
include "isabl2.mm"
include "sylanbrc.mm"

theorem archiabllem1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let cU: class U
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
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

  disjoint B x
  disjoint U x
  disjoint W x
  disjoint ph x
  disjoint .x. x
  disjoint .0. x
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
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B n
  disjoint B y
  disjoint B z
  disjoint U m
  disjoint U n
  disjoint W m
  disjoint W n
  disjoint W y
  disjoint W z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint .x. m
  disjoint .x. n
  disjoint .0. m
  disjoint .0. n
  disjoint .< m
  disjoint .< n
  disjoint .<_ m
  assert |- ( ph -> W e. Abel )

  proof
    wph
    cW
    cgrp
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @2
    @1
    @3
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    cW
    cabl
    wcel
    wph
    cW
    cogrp
    wcel
    @0
    archiabllem.g
    cW
    ogrpgrp
    syl
    #
    wph
    @6
    vy
    vz
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    wa
    #
    @1
    vm
    cv
    #
    cU
    c.x
    co
    #
    wceq
    #
    @6
    vm
    cz
    @11
    @12
    cz
    wcel
    #
    wa
    #
    @14
    wa
    #
    @2
    vn
    cv
    #
    cU
    c.x
    co
    #
    wceq
    #
    @6
    vn
    cz
    @17
    @18
    cz
    wcel
    #
    wa
    #
    @20
    wa
    #
    @13
    @19
    @3
    co
    #
    @19
    @13
    @3
    co
    #
    @4
    @5
    @22
    @24
    @25
    wceq
    #
    @20
    @16
    @21
    @26
    @14
    wph
    @15
    @21
    @26
    @10
    wph
    @15
    wa
    #
    @21
    wa
    #
    @12
    @18
    caddc
    co
    #
    cU
    c.x
    co
    #
    @18
    @12
    caddc
    co
    #
    cU
    c.x
    co
    #
    @24
    @25
    @28
    @29
    @31
    cU
    c.x
    @28
    @12
    @18
    @28
    @12
    wph
    @15
    @21
    simplr
    #
    zcnd
    @28
    @18
    @27
    @21
    simpr
    #
    zcnd
    addcomd
    oveq1d
    @28
    @0
    @15
    @21
    cU
    cB
    wcel
    #
    @30
    @24
    wceq
    wph
    @0
    @15
    @21
    @7
    ad2antrr
    #
    @33
    @34
    wph
    @35
    @15
    @21
    archiabllem1.u
    ad2antrr
    #
    cB
    @3
    c.x
    cW
    @12
    @18
    cU
    archiabllem.b
    archiabllem.m
    @3
    eqid
    #
    mulgdir
    syl13anc
    @28
    @0
    @21
    @15
    @35
    @32
    @25
    wceq
    @36
    @34
    @33
    @37
    cB
    @3
    c.x
    cW
    @18
    @12
    cU
    archiabllem.b
    archiabllem.m
    @38
    mulgdir
    syl13anc
    3eqtr3d
    adantllr
    adantlr
    adantr
    @23
    @1
    @13
    @2
    @19
    @3
    @16
    @14
    @21
    @20
    simpllr
    #
    @22
    @20
    simpr
    #
    oveq12d
    @23
    @2
    @19
    @1
    @13
    @3
    @40
    @39
    oveq12d
    3eqtr4d
    @17
    wph
    @9
    @20
    vn
    cz
    wrex
    wph
    @10
    @15
    @14
    simplll
    wph
    @10
    @15
    @14
    @9
    @8
    @9
    @15
    @14
    wph
    simpr1r
    3anassrs
    wph
    vx
    vz
    cB
    c.lt
    c.x
    cU
    vn
    c.le
    cW
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    archiabllem.g
    archiabllem.a
    archiabllem1.u
    archiabllem1.p
    archiabllem1.s
    archiabllem1b
    syl2anc
    r19.29a
    wph
    @8
    @14
    vm
    cz
    wrex
    @9
    wph
    vx
    vy
    cB
    c.lt
    c.x
    cU
    vm
    c.le
    cW
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    archiabllem.g
    archiabllem.a
    archiabllem1.u
    archiabllem1.p
    archiabllem1.s
    archiabllem1b
    adantrr
    r19.29a
    ralrimivva
    vy
    vz
    cB
    @3
    cW
    archiabllem.b
    @38
    isabl2
    sylanbrc
end
