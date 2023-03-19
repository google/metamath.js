include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cq.mm"
include "relopabi.mm"
include "wbr.mm"
include "simplr.mm"
include "simpll.mm"
include "cneg.mm"
include "cc.mm"
include "cr.mm"
include "unitssre.mm"
include "sseli.mm"
include "recnd.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "negsubdi2d.mm"
include "qnegcl.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "jca31.mm"
include "wceq.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "brab2a.mm"
include "3imtr4i.mm"
include "simpl.mm"
include "sylib.mm"
include "simpld.mm"
include "simpr.mm"
include "simprd.mm"
include "jca.mm"
include "caddc.mm"
include "syl.mm"
include "sseldi.mm"
include "npncand.mm"
include "qaddcl.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "subidd.mm"
include "cz.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "pm4.24.mm"
include "3bitr4i.mm"
include "iseri.mm"

theorem vitalilem1
  let vx: setvar x
  let vy: setvar y
  let c.sm: class .~
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let cG: class G
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let vu: setvar u
  assume vitali.1: |- .~ = { <. x , y >. | ( ( x e. ( 0 [,] 1 ) /\ y e. ( 0 [,] 1 ) ) /\ ( x - y ) e. QQ ) }

  disjoint x y
  disjoint .~ x
  disjoint .~ y
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint k m
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint k ph
  disjoint m v
  disjoint m w
  disjoint m ph
  disjoint n v
  disjoint n w
  disjoint n ph
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w z
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint S w
  disjoint S z
  disjoint T k
  disjoint T m
  disjoint T v
  disjoint T w
  disjoint T x
  disjoint k s
  disjoint k y
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint s v
  disjoint s w
  disjoint F s
  disjoint v y
  disjoint F v
  disjoint w y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint m u
  disjoint .~ m
  disjoint n u
  disjoint .~ n
  disjoint s u
  disjoint .~ s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .~ u
  disjoint .~ v
  disjoint .~ w
  disjoint .~ z
  assert |- .~ Er ( 0 [,] 1 )

  proof
    vu
    vv
    vw
    cc0
    c1
    cicc
    co
    #
    c.sm
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    #
    @0
    wcel
    wa
    @1
    @2
    cmin
    co
    #
    cq
    wcel
    #
    wa
    vx
    vy
    c.sm
    vitali.1
    relopabi
    vu
    cv
    #
    @0
    wcel
    #
    vv
    cv
    #
    @0
    wcel
    #
    wa
    #
    @5
    @7
    cmin
    co
    #
    cq
    wcel
    #
    wa
    #
    @8
    @6
    wa
    @7
    @5
    cmin
    co
    #
    cq
    wcel
    #
    wa
    @5
    @7
    c.sm
    wbr
    #
    @7
    @5
    c.sm
    wbr
    @12
    @8
    @6
    @14
    @6
    @8
    @11
    simplr
    @6
    @8
    @11
    simpll
    @12
    @10
    cneg
    #
    @13
    cq
    @12
    @5
    @7
    @6
    @5
    cc
    wcel
    #
    @8
    @11
    @6
    @5
    @0
    cr
    @5
    unitssre
    sseli
    recnd
    #
    ad2antrr
    @8
    @7
    cc
    wcel
    #
    @6
    @11
    @8
    @7
    @0
    cr
    @7
    unitssre
    sseli
    recnd
    ad2antlr
    #
    negsubdi2d
    @11
    @16
    cq
    wcel
    @9
    @10
    qnegcl
    adantl
    eqeltrrd
    jca31
    @4
    @11
    vx
    vy
    @5
    @7
    @0
    @0
    c.sm
    @1
    @5
    wceq
    #
    @2
    @7
    wceq
    wa
    @3
    @10
    cq
    @1
    @5
    @2
    @7
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    #
    @4
    @14
    vx
    vy
    @7
    @5
    @0
    @0
    c.sm
    @1
    @7
    wceq
    #
    @2
    @5
    wceq
    #
    wa
    @3
    @13
    cq
    @1
    @7
    @2
    @5
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    3imtr4i
    @15
    @7
    vw
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @6
    @25
    @0
    wcel
    #
    wa
    @5
    @25
    cmin
    co
    #
    cq
    wcel
    #
    @5
    @25
    c.sm
    wbr
    @27
    @6
    @28
    @27
    @6
    @8
    @27
    @9
    @11
    @27
    @15
    @12
    @15
    @26
    simpl
    @22
    sylib
    #
    simpld
    simpld
    #
    @27
    @8
    @28
    @27
    @8
    @28
    wa
    #
    @7
    @25
    cmin
    co
    #
    cq
    wcel
    #
    @27
    @26
    @33
    @35
    wa
    @15
    @26
    simpr
    @4
    @35
    vx
    vy
    @7
    @25
    @0
    @0
    c.sm
    @23
    @2
    @25
    wceq
    #
    wa
    @3
    @34
    cq
    @1
    @7
    @2
    @25
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    sylib
    #
    simpld
    simprd
    #
    jca
    @27
    @10
    @34
    caddc
    co
    #
    @29
    cq
    @27
    @5
    @7
    @25
    @27
    @6
    @17
    @32
    @18
    syl
    @27
    @12
    @19
    @31
    @20
    syl
    @27
    @25
    @27
    @0
    cr
    @25
    unitssre
    @38
    sseldi
    recnd
    npncand
    @27
    @11
    @35
    @39
    cq
    wcel
    @27
    @9
    @11
    @31
    simprd
    @27
    @33
    @35
    @37
    simprd
    @10
    @34
    qaddcl
    syl2anc
    eqeltrrd
    @4
    @30
    vx
    vy
    @5
    @25
    @0
    @0
    c.sm
    @21
    @36
    wa
    @3
    @29
    cq
    @1
    @5
    @2
    @25
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    sylanbrc
    @6
    @6
    wa
    #
    @40
    @5
    @5
    cmin
    co
    #
    cq
    wcel
    #
    wa
    @6
    @5
    @5
    c.sm
    wbr
    @40
    @42
    @6
    @42
    @6
    @6
    @41
    cc0
    cq
    @6
    @5
    @18
    subidd
    cc0
    cz
    wcel
    cc0
    cq
    wcel
    0z
    cc0
    zq
    ax-mp
    syl6eqel
    adantr
    pm4.71i
    @6
    pm4.24
    @4
    @42
    vx
    vy
    @5
    @5
    @0
    @0
    c.sm
    @21
    @24
    wa
    @3
    @41
    cq
    @1
    @5
    @2
    @5
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    3bitr4i
    iseri
end
