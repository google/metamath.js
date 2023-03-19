include "chpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "rexbidv.mm"
include "hpgbr.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem hpgcom
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
  let vx: setvar x
  assume hpgid.p: |- P = ( Base ` G )
  assume hpgid.i: |- I = ( Itv ` G )
  assume hpgid.l: |- L = ( LineG ` G )
  assume hpgid.g: |- ( ph -> G e. TarskiG )
  assume hpgid.d: |- ( ph -> D e. ran L )
  assume hpgid.a: |- ( ph -> A e. P )
  assume hpgid.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume hpgcom.b: |- ( ph -> B e. P )
  assume hpgcom.1: |- ( ph -> A ( ( hpG ` G ) ` D ) B )

  disjoint A t
  disjoint B t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint ph t
  disjoint A c
  disjoint A x
  disjoint c t
  disjoint c x
  disjoint t x
  disjoint B c
  disjoint D c
  disjoint D x
  disjoint a c
  disjoint a x
  disjoint b c
  disjoint b x
  disjoint G c
  disjoint I c
  disjoint O x
  disjoint P c
  disjoint P x
  disjoint c ph
  disjoint ph x
  assert |- ( ph -> B ( ( hpG ` G ) ` D ) A )

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
    #
    cB
    cA
    @0
    wbr
    #
    hpgcom.1
    wph
    cA
    vc
    cv
    #
    cO
    wbr
    #
    cB
    @3
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    @5
    @4
    wa
    #
    vc
    cP
    wrex
    @1
    @2
    wph
    @6
    @7
    vc
    cP
    @6
    @7
    wb
    wph
    @4
    @5
    ancom
    a1i
    rexbidv
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    vc
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.o
    hpgid.g
    hpgid.d
    hpgid.a
    hpgcom.b
    hpgbr
    wph
    vt
    cB
    cA
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    vc
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.o
    hpgid.g
    hpgid.d
    hpgcom.b
    hpgid.a
    hpgbr
    3bitr4d
    mpbid
end
