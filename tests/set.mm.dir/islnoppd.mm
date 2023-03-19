include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wceq.mm"
include "simpr.mm"
include "eleq1d.mm"
include "rspcedvd.mm"
include "jca31.mm"
include "islnopp.mm"
include "mpbird.mm"

theorem islnoppd
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume islnoppd.a: |- ( ph -> A e. P )
  assume islnoppd.b: |- ( ph -> B e. P )
  assume islnoppd.c: |- ( ph -> C e. D )
  assume islnoppd.1: |- ( ph -> -. A e. D )
  assume islnoppd.2: |- ( ph -> -. B e. D )
  assume islnoppd.3: |- ( ph -> C e. ( A I B ) )

  disjoint A t
  disjoint B t
  disjoint C t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint P a
  disjoint P b
  disjoint ph t
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  assert |- ( ph -> A O B )

  proof
    wph
    cA
    cB
    cO
    wbr
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
    wph
    @0
    @1
    @5
    islnoppd.1
    islnoppd.2
    wph
    @4
    cC
    @3
    wcel
    vt
    cC
    cD
    islnoppd.c
    wph
    @2
    cC
    wceq
    #
    wa
    @2
    cC
    @3
    wph
    @6
    simpr
    eleq1d
    islnoppd.3
    rspcedvd
    jca31
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    islnoppd.a
    islnoppd.b
    islnopp
    mpbird
end
