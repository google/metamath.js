include "c0.mm"
include "wceq.mm"
include "wral.mm"
include "cin.mm"
include "ciun.mm"
include "cdif.mm"
include "cun.mm"
include "wss.mm"
include "inss2.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "nfcv.mm"
include "nfin.mm"
include "ssrexf.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "ax-mp.mm"
include "iuneq2.mm"
include "iun0.mm"
include "syl6eq.mm"
include "syl5sseq.mm"
include "ss0.mm"
include "syl.mm"
include "uneq1d.mm"
include "iunxun.mm"
include "inundif.mm"
include "nfth.mm"
include "nfdif.mm"
include "nfun.mm"
include "id.mm"
include "eqidd.mm"
include "iuneq12df.mm"
include "eqtr3i.mm"
include "a1i.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "3eqtr3rd.mm"

theorem iunxdif3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let vy: setvar y
  assume iunxdif3.1: |- F/_ x E

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint E y
  assert |- ( A. x e. E B = (/) -> U_ x e. ( A \ E ) B = U_ x e. A B )

  proof
    cB
    c0
    wceq
    vx
    cE
    wral
    #
    vx
    cA
    cE
    cin
    #
    cB
    ciun
    #
    vx
    cA
    cE
    cdif
    #
    cB
    ciun
    #
    cun
    #
    c0
    @4
    cun
    #
    vx
    cA
    cB
    ciun
    #
    @4
    @0
    @2
    c0
    @4
    @0
    @2
    c0
    wss
    @2
    c0
    wceq
    @0
    vx
    cE
    cB
    ciun
    #
    @2
    c0
    @1
    cE
    wss
    #
    @2
    @8
    wss
    cA
    cE
    inss2
    @9
    vy
    @2
    @8
    @9
    vy
    cv
    #
    cB
    wcel
    #
    vx
    @1
    wrex
    @11
    vx
    cE
    wrex
    @10
    @2
    wcel
    @10
    @8
    wcel
    @11
    vx
    @1
    cE
    vx
    cA
    cE
    vx
    cA
    nfcv
    #
    iunxdif3.1
    nfin
    #
    iunxdif3.1
    ssrexf
    vx
    @10
    @1
    cB
    eliun
    vx
    @10
    cE
    cB
    eliun
    3imtr4g
    ssrdv
    ax-mp
    @0
    @8
    vx
    cE
    c0
    ciun
    c0
    vx
    cE
    cB
    c0
    iuneq2
    vx
    cE
    iun0
    syl6eq
    syl5sseq
    @2
    ss0
    syl
    uneq1d
    @5
    @7
    wceq
    @0
    vx
    @1
    @3
    cun
    #
    cB
    ciun
    #
    @5
    @7
    vx
    @1
    @3
    cB
    iunxun
    @14
    cA
    wceq
    #
    @15
    @7
    wceq
    cA
    cE
    inundif
    #
    @16
    vx
    @14
    cA
    cB
    cB
    @16
    vx
    @17
    nfth
    vx
    @1
    @3
    @13
    vx
    cA
    cE
    @12
    iunxdif3.1
    nfdif
    nfun
    @12
    @16
    id
    @16
    cB
    eqidd
    iuneq12df
    ax-mp
    eqtr3i
    a1i
    @6
    @4
    wceq
    @0
    @6
    @4
    c0
    cun
    @4
    c0
    @4
    uncom
    @4
    un0
    eqtri
    a1i
    3eqtr3rd
end
