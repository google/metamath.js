include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "ccgrg.mm"
include "cgr3simp1.mm"
include "tgcgrneq.mm"
include "hlid.mm"
include "cgr3simp2.mm"
include "tgcgrcomlr.mm"
include "necomd.mm"
include "iscgrad.mm"

theorem cgrcgra
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume cgraid.p: |- P = ( Base ` G )
  assume cgraid.i: |- I = ( Itv ` G )
  assume cgraid.g: |- ( ph -> G e. TarskiG )
  assume cgraid.k: |- K = ( hlG ` G )
  assume cgraid.a: |- ( ph -> A e. P )
  assume cgraid.b: |- ( ph -> B e. P )
  assume cgraid.c: |- ( ph -> C e. P )
  assume cgracom.d: |- ( ph -> D e. P )
  assume cgracom.e: |- ( ph -> E e. P )
  assume cgracom.f: |- ( ph -> F e. P )
  assume cgrcgra.1: |- ( ph -> A =/= B )
  assume cgrcgra.2: |- ( ph -> B =/= C )
  assume cgrcgra.3: |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E F "> )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    cK
    cD
    cF
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgracom.d
    cgracom.f
    cgrcgra.3
    wph
    cD
    cA
    cE
    cP
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgracom.d
    cgraid.a
    cgracom.e
    cgraid.g
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cgraid.p
    @0
    eqid
    #
    cgraid.i
    cgraid.g
    cgraid.a
    cgraid.b
    cgracom.d
    cgracom.e
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    ccgrg
    cfv
    #
    cE
    cF
    cG
    cI
    @0
    cgraid.p
    @1
    cgraid.i
    @2
    eqid
    #
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgrcgra.3
    cgr3simp1
    cgrcgra.1
    tgcgrneq
    hlid
    wph
    cF
    cA
    cE
    cP
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgracom.f
    cgraid.a
    cgracom.e
    cgraid.g
    wph
    cC
    cB
    cF
    cE
    cP
    cG
    cI
    @0
    cgraid.p
    @1
    cgraid.i
    cgraid.g
    cgraid.c
    cgraid.b
    cgracom.f
    cgracom.e
    wph
    cB
    cC
    cE
    cF
    cP
    cG
    cI
    @0
    cgraid.p
    @1
    cgraid.i
    cgraid.g
    cgraid.b
    cgraid.c
    cgracom.e
    cgracom.f
    wph
    cA
    cB
    cC
    cD
    cP
    @2
    cE
    cF
    cG
    cI
    @0
    cgraid.p
    @1
    cgraid.i
    @3
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgrcgra.3
    cgr3simp2
    tgcgrcomlr
    wph
    cB
    cC
    cgrcgra.2
    necomd
    tgcgrneq
    hlid
    iscgrad
end
