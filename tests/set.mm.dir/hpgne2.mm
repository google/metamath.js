include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "crn.mm"
include "ad2antrr.mm"
include "cstrkg.mm"
include "simplr.mm"
include "simprr.mm"
include "oppne1.mm"
include "chpg.mm"
include "wrex.mm"
include "hpgbr.mm"
include "mpbid.mm"
include "r19.29a.mm"

theorem hpgne2
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
  assume ishpg.p: |- P = ( Base ` G )
  assume ishpg.i: |- I = ( Itv ` G )
  assume ishpg.l: |- L = ( LineG ` G )
  assume ishpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume ishpg.g: |- ( ph -> G e. TarskiG )
  assume ishpg.d: |- ( ph -> D e. ran L )
  assume hpgbr.a: |- ( ph -> A e. P )
  assume hpgbr.b: |- ( ph -> B e. P )
  assume hpgne1.1: |- ( ph -> A ( ( hpG ` G ) ` D ) B )

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
  disjoint L t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint ph t
  disjoint A c
  disjoint c t
  disjoint B c
  disjoint D c
  disjoint a c
  disjoint b c
  disjoint I c
  disjoint P c
  disjoint c ph
  assert |- ( ph -> -. B e. D )

  proof
    wph
    cA
    vc
    cv
    #
    cO
    wbr
    #
    cB
    @0
    cO
    wbr
    #
    wa
    #
    cB
    cD
    wcel
    wn
    vc
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @3
    wa
    vt
    cB
    @0
    cD
    cP
    cG
    cI
    cL
    cG
    cds
    cfv
    #
    cO
    va
    vb
    ishpg.p
    @6
    eqid
    ishpg.i
    ishpg.o
    ishpg.l
    wph
    cD
    cL
    crn
    wcel
    @4
    @3
    ishpg.d
    ad2antrr
    wph
    cG
    cstrkg
    wcel
    @4
    @3
    ishpg.g
    ad2antrr
    wph
    cB
    cP
    wcel
    @4
    @3
    hpgbr.b
    ad2antrr
    wph
    @4
    @3
    simplr
    @5
    @1
    @2
    simprr
    oppne1
    wph
    cA
    cB
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    @3
    vc
    cP
    wrex
    hpgne1.1
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
    ishpg.p
    ishpg.i
    ishpg.l
    ishpg.o
    ishpg.g
    ishpg.d
    hpgbr.a
    hpgbr.b
    hpgbr
    mpbid
    r19.29a
end
