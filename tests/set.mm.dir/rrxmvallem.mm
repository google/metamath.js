include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "cc0.mm"
include "wne.mm"
include "crab.mm"
include "cun.mm"
include "csupp.mm"
include "wo.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "cc.mm"
include "simprl.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "simprr.mm"
include "eqtr4d.mm"
include "subeq0bd.mm"
include "sq0id.mm"
include "ex.mm"
include "wb.mm"
include "ioran.mm"
include "nne.mm"
include "anbi12i.mm"
include "bitri.mm"
include "a1i.mm"
include "cvv.mm"
include "eqidd.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmptd.mm"
include "neeq1d.mm"
include "bicomd.mm"
include "necon1bbid.mm"
include "3imtr4d.mm"
include "con4d.mm"
include "ss2rabdv.mm"
include "unrab.mm"
include "syl6sseqr.mm"
include "simp1.mm"
include "wfn.mm"
include "eqid.mm"
include "fnmpti.mm"
include "suppvalfn.mm"
include "mp3an13.mm"
include "syl.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "elmapi.mm"
include "ffn.mm"
include "3syl.mm"
include "3ad2ant2.mm"
include "syl3anc.mm"
include "3ad2ant3.mm"
include "uneq12d.mm"
include "3sstr4d.mm"

theorem rrxmvallem
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }

  disjoint F h
  disjoint F k
  disjoint h k
  disjoint G h
  disjoint G k
  disjoint I h
  disjoint I k
  disjoint V h
  disjoint V k
  disjoint X k
  disjoint A k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( I e. V /\ F e. X /\ G e. X ) -> ( ( k e. I |-> ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) ) supp 0 ) C_ ( ( F supp 0 ) u. ( G supp 0 ) ) )

  proof
    cI
    cV
    wcel
    #
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    w3a
    #
    vx
    cv
    #
    vk
    cI
    vk
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cfv
    #
    cc0
    wne
    #
    vx
    cI
    crab
    #
    @4
    cF
    cfv
    #
    cc0
    wne
    #
    vx
    cI
    crab
    #
    @4
    cG
    cfv
    #
    cc0
    wne
    #
    vx
    cI
    crab
    #
    cun
    #
    @10
    cc0
    csupp
    co
    #
    cF
    cc0
    csupp
    co
    #
    cG
    cc0
    csupp
    co
    #
    cun
    @3
    @13
    @15
    @18
    wo
    #
    vx
    cI
    crab
    @20
    @3
    @12
    @24
    vx
    cI
    @3
    @4
    cI
    wcel
    #
    wa
    #
    @24
    @12
    @26
    @14
    cc0
    wceq
    #
    @17
    cc0
    wceq
    #
    wa
    #
    @14
    @17
    cmin
    co
    #
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @24
    wn
    #
    @12
    wn
    @26
    @29
    @32
    @26
    @29
    wa
    #
    @30
    @34
    @14
    @17
    @34
    @14
    cc0
    cc
    @26
    @27
    @28
    simprl
    #
    0cn
    syl6eqel
    @34
    @14
    cc0
    @17
    @35
    @26
    @27
    @28
    simprr
    eqtr4d
    subeq0bd
    sq0id
    ex
    @33
    @29
    wb
    @26
    @33
    @15
    wn
    #
    @18
    wn
    #
    wa
    @29
    @15
    @18
    ioran
    @36
    @27
    @37
    @28
    @14
    cc0
    nne
    @17
    cc0
    nne
    anbi12i
    bitri
    a1i
    @26
    @12
    @31
    cc0
    @26
    @12
    @31
    cc0
    wne
    @26
    @11
    @31
    cc0
    @26
    vk
    @4
    @9
    @31
    cI
    @10
    cvv
    @26
    @10
    eqidd
    @26
    @5
    @4
    wceq
    #
    wa
    #
    @8
    @30
    c2
    cexp
    @39
    @6
    @14
    @7
    @17
    cmin
    @39
    @5
    @4
    cF
    @26
    @38
    simpr
    #
    fveq2d
    @39
    @5
    @4
    cG
    @40
    fveq2d
    oveq12d
    oveq1d
    @3
    @25
    simpr
    @31
    cvv
    wcel
    @26
    @30
    c2
    cexp
    ovex
    a1i
    fvmptd
    neeq1d
    bicomd
    necon1bbid
    3imtr4d
    con4d
    ss2rabdv
    @15
    @18
    vx
    cI
    unrab
    syl6sseqr
    @3
    @0
    @21
    @13
    wceq
    #
    @0
    @1
    @2
    simp1
    #
    @10
    cI
    wfn
    @0
    cc0
    cc
    wcel
    #
    @41
    vk
    cI
    @9
    @10
    @8
    c2
    cexp
    ovex
    @10
    eqid
    fnmpti
    0cn
    vx
    @10
    cV
    cc
    cI
    cc0
    suppvalfn
    mp3an13
    syl
    @3
    @22
    @16
    @23
    @19
    @3
    cF
    cI
    wfn
    #
    @0
    @43
    @22
    @16
    wceq
    @1
    @0
    @44
    @2
    @1
    cF
    cr
    cI
    cmap
    co
    #
    wcel
    #
    cI
    cr
    cF
    wf
    @44
    @46
    cF
    vh
    cv
    cc0
    cfsupp
    wbr
    #
    vh
    @45
    crab
    #
    cX
    @47
    vh
    cF
    @45
    elrabi
    rrxmval.1
    eleq2s
    cF
    cr
    cI
    elmapi
    cI
    cr
    cF
    ffn
    3syl
    3ad2ant2
    @42
    @43
    @3
    0cn
    a1i
    #
    vx
    cF
    cV
    cc
    cI
    cc0
    suppvalfn
    syl3anc
    @3
    cG
    cI
    wfn
    #
    @0
    @43
    @23
    @19
    wceq
    @2
    @0
    @50
    @1
    @2
    cG
    @45
    wcel
    #
    cI
    cr
    cG
    wf
    @50
    @51
    cG
    @48
    cX
    @47
    vh
    cG
    @45
    elrabi
    rrxmval.1
    eleq2s
    cG
    cr
    cI
    elmapi
    cI
    cr
    cG
    ffn
    3syl
    3ad2ant3
    @42
    @49
    vx
    cG
    cV
    cc
    cI
    cc0
    suppvalfn
    syl3anc
    uneq12d
    3sstr4d
end
