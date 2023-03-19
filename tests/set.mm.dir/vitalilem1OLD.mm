include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cq.mm"
include "relopabi.mm"
include "a1i.mm"
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
include "weq.mm"
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
include "wb.mm"
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
include "iserd.mm"
include "trud.mm"

theorem vitalilem1OLD
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
    cc0
    c1
    cicc
    co
    #
    c.sm
    wer
    wtru
    vu
    vv
    vw
    @0
    c.sm
    c.sm
    wrel
    wtru
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
    a1i
    vu
    cv
    #
    vv
    cv
    #
    c.sm
    wbr
    #
    @6
    @5
    c.sm
    wbr
    #
    wtru
    @5
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    @5
    @6
    cmin
    co
    #
    cq
    wcel
    #
    wa
    #
    @10
    @9
    wa
    @6
    @5
    cmin
    co
    #
    cq
    wcel
    #
    wa
    @7
    @8
    @14
    @10
    @9
    @16
    @9
    @10
    @13
    simplr
    @9
    @10
    @13
    simpll
    @14
    @12
    cneg
    #
    @15
    cq
    @14
    @5
    @6
    @9
    @5
    cc
    wcel
    #
    @10
    @13
    @9
    @5
    @0
    cr
    @5
    unitssre
    sseli
    recnd
    #
    ad2antrr
    @10
    @6
    cc
    wcel
    #
    @9
    @13
    @10
    @6
    @0
    cr
    @6
    unitssre
    sseli
    recnd
    ad2antlr
    #
    negsubdi2d
    @13
    @17
    cq
    wcel
    @11
    @12
    qnegcl
    adantl
    eqeltrrd
    jca31
    @4
    @13
    vx
    vy
    @5
    @6
    @0
    @0
    c.sm
    vx
    vu
    weq
    #
    vy
    vv
    weq
    wa
    @3
    @12
    cq
    @1
    @5
    @2
    @6
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    #
    @4
    @16
    vx
    vy
    @6
    @5
    @0
    @0
    c.sm
    vx
    vv
    weq
    #
    vy
    vu
    weq
    #
    wa
    @3
    @15
    cq
    @1
    @6
    @2
    @5
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    3imtr4i
    adantl
    @7
    @6
    vw
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @5
    @26
    c.sm
    wbr
    #
    wtru
    @28
    @9
    @26
    @0
    wcel
    #
    wa
    @5
    @26
    cmin
    co
    #
    cq
    wcel
    #
    @29
    @28
    @9
    @30
    @28
    @9
    @10
    @28
    @11
    @13
    @28
    @7
    @14
    @7
    @27
    simpl
    @23
    sylib
    #
    simpld
    simpld
    #
    @28
    @10
    @30
    @28
    @10
    @30
    wa
    #
    @6
    @26
    cmin
    co
    #
    cq
    wcel
    #
    @28
    @27
    @35
    @37
    wa
    @7
    @27
    simpr
    @4
    @37
    vx
    vy
    @6
    @26
    @0
    @0
    c.sm
    @24
    vy
    vw
    weq
    #
    wa
    @3
    @36
    cq
    @1
    @6
    @2
    @26
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
    @28
    @12
    @36
    caddc
    co
    #
    @31
    cq
    @28
    @5
    @6
    @26
    @28
    @9
    @18
    @34
    @19
    syl
    @28
    @14
    @20
    @33
    @21
    syl
    @28
    @26
    @28
    @0
    cr
    @26
    unitssre
    @40
    sseldi
    recnd
    npncand
    @28
    @13
    @37
    @41
    cq
    wcel
    @28
    @11
    @13
    @33
    simprd
    @28
    @35
    @37
    @39
    simprd
    @12
    @36
    qaddcl
    syl2anc
    eqeltrrd
    @4
    @32
    vx
    vy
    @5
    @26
    @0
    @0
    c.sm
    @22
    @38
    wa
    @3
    @31
    cq
    @1
    @5
    @2
    @26
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    sylanbrc
    adantl
    @9
    @5
    @5
    c.sm
    wbr
    #
    wb
    wtru
    @9
    @9
    wa
    #
    @43
    @5
    @5
    cmin
    co
    #
    cq
    wcel
    #
    wa
    @9
    @42
    @43
    @45
    @9
    @45
    @9
    @9
    @44
    cc0
    cq
    @9
    @5
    @19
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
    @9
    pm4.24
    @4
    @45
    vx
    vy
    @5
    @5
    @0
    @0
    c.sm
    @22
    @25
    wa
    @3
    @44
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
    a1i
    iserd
    trud
end
