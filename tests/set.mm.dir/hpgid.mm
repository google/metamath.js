include "chpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "simprr.mm"
include "jca.mm"
include "hpgerlem.mm"
include "reximddv.mm"
include "hpgbr.mm"
include "mpbird.mm"

theorem hpgid
  let wph: wff ph
  let vt: setvar t
  let cA: class A
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
  let cB: class B
  assume hpgid.p: |- P = ( Base ` G )
  assume hpgid.i: |- I = ( Itv ` G )
  assume hpgid.l: |- L = ( LineG ` G )
  assume hpgid.g: |- ( ph -> G e. TarskiG )
  assume hpgid.d: |- ( ph -> D e. ran L )
  assume hpgid.a: |- ( ph -> A e. P )
  assume hpgid.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume hpgid.1: |- ( ph -> -. A e. D )

  disjoint A t
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
  disjoint B t
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
  assert |- ( ph -> A ( ( hpG ` G ) ` D ) A )

  proof
    wph
    cA
    cA
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    cA
    vc
    cv
    #
    cO
    wbr
    #
    @1
    wa
    #
    vc
    cP
    wrex
    wph
    @1
    @2
    vc
    cP
    wph
    @0
    cP
    wcel
    #
    @1
    wa
    wa
    @1
    @1
    wph
    @3
    @1
    simprr
    #
    @4
    jca
    wph
    vt
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
    hpgid.g
    hpgid.d
    hpgid.a
    hpgid.o
    hpgid.1
    hpgerlem
    reximddv
    wph
    vt
    cA
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
    hpgid.a
    hpgid.a
    hpgbr
    mpbird
end
