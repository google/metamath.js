include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cep.mm"
include "cv.mm"
include "wiso.mm"
include "wex.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "resiexg.mm"
include "isoid.mm"
include "isoeq1.mm"
include "spcegv.mm"
include "mpisyl.mm"
include "adantr.mm"
include "isoeq5.mm"
include "exbidv.mm"
include "syl5ibcom.mm"
include "word.mm"
include "wi.mm"
include "eloni.mm"
include "ordiso2.mm"
include "3coml.mm"
include "3expia.mm"
include "syl2an.mm"
include "exlimdv.mm"
include "impbid.mm"

theorem ordiso
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F

  disjoint A f
  disjoint B f
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( ( A e. On /\ B e. On ) -> ( A = B <-> E. f f Isom _E , _E ( A , B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cep
    cep
    vf
    cv
    #
    wiso
    #
    vf
    wex
    #
    @2
    cA
    cA
    cep
    cep
    @4
    wiso
    #
    vf
    wex
    #
    @3
    @6
    @0
    @8
    @1
    @0
    cid
    cA
    cres
    #
    cvv
    wcel
    cA
    cA
    cep
    cep
    @9
    wiso
    #
    @8
    cA
    con0
    resiexg
    cA
    cep
    isoid
    @7
    @10
    vf
    @9
    cvv
    cA
    cA
    cep
    cep
    @9
    @4
    isoeq1
    spcegv
    mpisyl
    adantr
    @3
    @7
    @5
    vf
    cA
    cA
    cB
    cep
    cep
    @4
    isoeq5
    exbidv
    syl5ibcom
    @2
    @5
    @3
    vf
    @0
    cA
    word
    #
    cB
    word
    #
    @5
    @3
    wi
    @1
    cA
    eloni
    cB
    eloni
    @11
    @12
    @5
    @3
    @5
    @11
    @12
    @3
    cA
    cB
    @4
    ordiso2
    3coml
    3expia
    syl2an
    exlimdv
    impbid
end
