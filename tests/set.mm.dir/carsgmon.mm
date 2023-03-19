include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ssexd.mm"
include "id.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "sseq1.mm"
include "3anbi2d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "eleq1.mm"
include "3anbi23d.mm"
include "breq2d.mm"
include "vtocl2g.mm"
include "imp.mm"
include "syl23anc.mm"

theorem carsgmon
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgmon.1: |- ( ph -> A C_ B )
  assume carsgmon.2: |- ( ph -> B e. ~P O )
  assume carsgmon.3: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  assert |- ( ph -> ( M ` A ) <_ ( M ` B ) )

  proof
    wph
    cA
    cvv
    wcel
    #
    cB
    cO
    cpw
    #
    wcel
    #
    wph
    cA
    cB
    wss
    #
    @2
    cA
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    cle
    wbr
    #
    wph
    cA
    cB
    @1
    carsgmon.2
    carsgmon.1
    ssexd
    carsgmon.2
    wph
    id
    carsgmon.1
    carsgmon.2
    @0
    @2
    wa
    wph
    @3
    @2
    w3a
    #
    @6
    wph
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    @9
    @1
    wcel
    #
    w3a
    #
    @8
    cM
    cfv
    #
    @9
    cM
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    cA
    @9
    wss
    #
    @11
    w3a
    #
    @4
    @14
    cle
    wbr
    #
    wi
    @7
    @6
    wi
    vx
    vy
    cA
    cB
    cvv
    @1
    @8
    cA
    wceq
    #
    @12
    @17
    @15
    @18
    @19
    @10
    @16
    wph
    @11
    @8
    cA
    @9
    sseq1
    3anbi2d
    @19
    @13
    @4
    @14
    cle
    @8
    cA
    cM
    fveq2
    breq1d
    imbi12d
    @9
    cB
    wceq
    #
    @17
    @7
    @18
    @6
    @20
    @16
    @3
    @11
    @2
    wph
    @9
    cB
    cA
    sseq2
    @9
    cB
    @1
    eleq1
    3anbi23d
    @20
    @14
    @5
    @4
    cle
    @9
    cB
    cM
    fveq2
    breq2d
    imbi12d
    carsgmon.3
    vtocl2g
    imp
    syl23anc
end
