include "chpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "hpgbr.mm"
include "mpbid.mm"
include "wcel.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "cstrkg.mm"
include "crn.mm"
include "simplr.mm"
include "simprr.mm"
include "lnopp2hpgb.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem hpgtr
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume hpgtr.c: |- ( ph -> C e. P )
  assume hpgtr.1: |- ( ph -> B ( ( hpG ` G ) ` D ) C )

  disjoint C a
  disjoint C b
  disjoint C t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint L a
  disjoint L b
  disjoint L t
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
  disjoint C c
  disjoint a c
  disjoint b c
  disjoint c t
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
  assert |- ( ph -> A ( ( hpG ` G ) ` D ) C )

  proof
    wph
    cA
    cC
    cD
    cG
    chpg
    cfv
    cfv
    #
    wbr
    cA
    vc
    cv
    #
    cO
    wbr
    #
    cC
    @1
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
    @2
    cB
    @1
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    #
    @5
    wph
    cA
    cB
    @0
    wbr
    @8
    hpgcom.1
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
    mpbid
    wph
    @7
    @4
    vc
    cP
    wph
    @1
    cP
    wcel
    #
    wa
    #
    @7
    @4
    @10
    @7
    wa
    #
    @2
    @3
    @10
    @2
    @6
    simprl
    @11
    @3
    cB
    cC
    @0
    wbr
    #
    wph
    @12
    @9
    @7
    hpgtr.1
    ad2antrr
    @11
    vt
    cB
    cC
    @1
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.o
    wph
    cG
    cstrkg
    wcel
    @9
    @7
    hpgid.g
    ad2antrr
    wph
    cD
    cL
    crn
    wcel
    @9
    @7
    hpgid.d
    ad2antrr
    wph
    cB
    cP
    wcel
    @9
    @7
    hpgcom.b
    ad2antrr
    wph
    cC
    cP
    wcel
    @9
    @7
    hpgtr.c
    ad2antrr
    wph
    @9
    @7
    simplr
    @10
    @2
    @6
    simprr
    lnopp2hpgb
    mpbird
    jca
    ex
    reximdva
    mpd
    wph
    vt
    cA
    cC
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
    hpgtr.c
    hpgbr
    mpbird
end
