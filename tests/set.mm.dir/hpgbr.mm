include "chpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "ishpg.mm"
include "wceq.mm"
include "simpl.mm"
include "breq1d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "cbvopabv.mm"
include "syl6eq.mm"
include "breqd.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "brabga.mm"
include "syl2anc.mm"
include "bitrd.mm"

theorem hpgbr
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  assume ishpg.p: |- P = ( Base ` G )
  assume ishpg.i: |- I = ( Itv ` G )
  assume ishpg.l: |- L = ( LineG ` G )
  assume ishpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume ishpg.g: |- ( ph -> G e. TarskiG )
  assume ishpg.d: |- ( ph -> D e. ran L )
  assume hpgbr.a: |- ( ph -> A e. P )
  assume hpgbr.b: |- ( ph -> B e. P )

  disjoint A c
  disjoint B c
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D t
  disjoint a b
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint G a
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I t
  disjoint O a
  disjoint O b
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P t
  disjoint A u
  disjoint A v
  disjoint c u
  disjoint c v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint O u
  disjoint O v
  disjoint a u
  disjoint a v
  disjoint b u
  disjoint b v
  disjoint P u
  disjoint P v
  disjoint t u
  disjoint t v
  assert |- ( ph -> ( A ( ( hpG ` G ) ` D ) B <-> E. c e. P ( A O c /\ B O c ) ) )

  proof
    wph
    cA
    cB
    cD
    cG
    chpg
    cfv
    cfv
    #
    wbr
    cA
    cB
    vu
    cv
    #
    vc
    cv
    #
    cO
    wbr
    #
    vv
    cv
    #
    @2
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    #
    vu
    vv
    copab
    #
    wbr
    #
    cA
    @2
    cO
    wbr
    #
    cB
    @2
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    #
    wph
    @0
    @8
    cA
    cB
    wph
    @0
    va
    cv
    #
    @2
    cO
    wbr
    #
    vb
    cv
    #
    @2
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    #
    va
    vb
    copab
    @8
    wph
    vt
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    vc
    ishpg.p
    ishpg.i
    ishpg.l
    ishpg.o
    ishpg.g
    ishpg.d
    ishpg
    @19
    @7
    va
    vb
    vu
    vv
    @14
    @1
    wceq
    #
    @16
    @4
    wceq
    #
    wa
    #
    @18
    @6
    vc
    cP
    @22
    @15
    @3
    @17
    @5
    @22
    @14
    @1
    @2
    cO
    @20
    @21
    simpl
    breq1d
    @22
    @16
    @4
    @2
    cO
    @20
    @21
    simpr
    breq1d
    anbi12d
    rexbidv
    cbvopabv
    syl6eq
    breqd
    wph
    cA
    cP
    wcel
    cB
    cP
    wcel
    @9
    @13
    wb
    hpgbr.a
    hpgbr.b
    @7
    @13
    vu
    vv
    cA
    cB
    @8
    cP
    cP
    @1
    cA
    wceq
    #
    @4
    cB
    wceq
    #
    wa
    #
    @6
    @12
    vc
    cP
    @25
    @3
    @10
    @5
    @11
    @25
    @1
    cA
    @2
    cO
    @23
    @24
    simpl
    breq1d
    @25
    @4
    cB
    @2
    cO
    @23
    @24
    simpr
    breq1d
    anbi12d
    rexbidv
    @8
    eqid
    brabga
    syl2anc
    bitrd
end
