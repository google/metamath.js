include "wbr.mm"
include "chpg.mm"
include "cfv.mm"
include "cds.mm"
include "eqid.mm"
include "oppnid.mm"
include "lnopp2hpgb.mm"
include "mtbid.mm"

theorem lnoppnhpg
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
  assume ishpg.p: |- P = ( Base ` G )
  assume ishpg.i: |- I = ( Itv ` G )
  assume ishpg.l: |- L = ( LineG ` G )
  assume ishpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume ishpg.g: |- ( ph -> G e. TarskiG )
  assume ishpg.d: |- ( ph -> D e. ran L )
  assume hpgbr.a: |- ( ph -> A e. P )
  assume hpgbr.b: |- ( ph -> B e. P )
  assume lnoppnhpg.1: |- ( ph -> A O B )

  disjoint A t
  disjoint B a
  disjoint B b
  disjoint B t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint ph t
  assert |- ( ph -> -. A ( ( hpG ` G ) ` D ) B )

  proof
    wph
    cB
    cB
    cO
    wbr
    cA
    cB
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    wph
    vt
    cB
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
    @0
    eqid
    ishpg.i
    ishpg.o
    ishpg.l
    ishpg.d
    ishpg.g
    hpgbr.b
    oppnid
    wph
    vt
    cA
    cB
    cB
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    ishpg.p
    ishpg.i
    ishpg.l
    ishpg.o
    ishpg.g
    ishpg.d
    hpgbr.a
    hpgbr.b
    hpgbr.b
    lnoppnhpg.1
    lnopp2hpgb
    mtbid
end
