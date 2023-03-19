include "chpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "jca.mm"
include "co.mm"
include "wceq.mm"
include "hlln.mm"
include "orcd.mm"
include "colrot2.mm"
include "colhp.mm"
include "mpbird.mm"

theorem hphl
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
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
  assume hphl.k: |- K = ( hlG ` G )
  assume hphl.a: |- ( ph -> A e. D )
  assume hphl.b: |- ( ph -> B e. P )
  assume hphl.c: |- ( ph -> C e. P )
  assume hphl.1: |- ( ph -> -. B e. D )
  assume hphl.2: |- ( ph -> B ( K ` A ) C )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint C t
  disjoint a t
  disjoint b t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint ph t
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
  assert |- ( ph -> B ( ( hpG ` G ) ` D ) C )

  proof
    wph
    cB
    cC
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    cB
    cC
    cA
    cK
    cfv
    wbr
    #
    cB
    cD
    wcel
    wn
    #
    wa
    wph
    @0
    @1
    hphl.2
    hphl.1
    jca
    wph
    vt
    cB
    cC
    cA
    cD
    cP
    cG
    cI
    cK
    cL
    cO
    va
    vb
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.g
    hpgid.d
    hphl.b
    hpgid.o
    hphl.c
    hphl.a
    wph
    cP
    cG
    cI
    cL
    cC
    cA
    cB
    hpgid.p
    hpgid.l
    hpgid.i
    hpgid.g
    hphl.c
    hpgid.a
    hphl.b
    wph
    cB
    cC
    cA
    cL
    co
    wcel
    cC
    cA
    wceq
    wph
    cB
    cC
    cA
    cP
    cG
    cI
    cK
    cL
    hpgid.p
    hpgid.i
    hphl.k
    hphl.b
    hphl.c
    hpgid.a
    hpgid.g
    hpgid.l
    hphl.2
    hlln
    orcd
    colrot2
    hphl.k
    colhp
    mpbird
end
