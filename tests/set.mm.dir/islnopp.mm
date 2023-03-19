include "wbr.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "id.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "copab.mm"
include "simpl.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "simpr.mm"
include "oveq12.mm"
include "cbvopabv.mm"
include "eqtri.mm"
include "brabg.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "eldif.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem islnopp
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume islnopp.a: |- ( ph -> A e. P )
  assume islnopp.b: |- ( ph -> B e. P )

  disjoint A t
  disjoint B t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A u
  disjoint A v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint D u
  disjoint D v
  disjoint I u
  disjoint I v
  disjoint P u
  disjoint P v
  disjoint a u
  disjoint a v
  disjoint b u
  disjoint b v
  assert |- ( ph -> ( A O B <-> ( ( -. A e. D /\ -. B e. D ) /\ E. t e. D t e. ( A I B ) ) ) )

  proof
    wph
    cA
    cB
    cO
    wbr
    #
    cA
    cP
    cD
    cdif
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    vt
    cv
    #
    cA
    cB
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    cA
    cD
    wcel
    wn
    #
    cB
    cD
    wcel
    wn
    #
    wa
    #
    @8
    wa
    wph
    cA
    cP
    wcel
    #
    cB
    cP
    wcel
    #
    @0
    @9
    wb
    islnopp.a
    islnopp.b
    vu
    cv
    #
    @1
    wcel
    #
    vv
    cv
    #
    @1
    wcel
    #
    wa
    #
    @5
    @15
    @17
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    @2
    @18
    wa
    #
    @5
    cA
    @17
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    @9
    vu
    vv
    cA
    cB
    cP
    cP
    cO
    @15
    cA
    wceq
    #
    @19
    @24
    @22
    @27
    @28
    @16
    @2
    @18
    @15
    cA
    @1
    eleq1
    anbi1d
    @28
    @21
    @26
    vt
    cD
    @28
    @20
    @25
    @5
    @28
    @15
    cA
    @17
    cI
    @28
    id
    oveq1d
    eleq2d
    rexbidv
    anbi12d
    @17
    cB
    wceq
    #
    @24
    @4
    @27
    @8
    @29
    @18
    @3
    @2
    @17
    cB
    @1
    eleq1
    anbi2d
    @29
    @26
    @7
    vt
    cD
    @29
    @25
    @6
    @5
    @17
    cB
    cA
    cI
    oveq2
    eleq2d
    rexbidv
    anbi12d
    cO
    va
    cv
    #
    @1
    wcel
    #
    vb
    cv
    #
    @1
    wcel
    #
    wa
    #
    @5
    @30
    @32
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    va
    vb
    copab
    @23
    vu
    vv
    copab
    hpg.o
    @38
    @23
    va
    vb
    vu
    vv
    @30
    @15
    wceq
    #
    @32
    @17
    wceq
    #
    wa
    #
    @34
    @19
    @37
    @22
    @41
    @31
    @16
    @33
    @18
    @41
    @30
    @15
    @1
    @1
    @39
    @40
    simpl
    @41
    @1
    eqidd
    #
    eleq12d
    @41
    @32
    @17
    @1
    @1
    @39
    @40
    simpr
    @42
    eleq12d
    anbi12d
    @41
    @36
    @21
    vt
    cD
    @41
    @35
    @20
    @5
    @30
    @15
    @32
    @17
    cI
    oveq12
    eleq2d
    rexbidv
    anbi12d
    cbvopabv
    eqtri
    brabg
    syl2anc
    wph
    @12
    @4
    @8
    wph
    @10
    @2
    @11
    @3
    wph
    @10
    @13
    @10
    wa
    @2
    wph
    @13
    @10
    islnopp.a
    biantrurd
    cA
    cP
    cD
    eldif
    syl6bbr
    wph
    @11
    @14
    @11
    wa
    @3
    wph
    @14
    @11
    islnopp.b
    biantrurd
    cB
    cP
    cD
    eldif
    syl6bbr
    anbi12d
    anbi1d
    bitr4d
end
