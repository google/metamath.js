include "cq.mm"
include "wcel.mm"
include "cdiv.mm"
include "cz.mm"
include "cn.mm"
include "cxp.mm"
include "cima.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "df-q.mm"
include "eleq2i.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "cmul.mm"
include "crio.mm"
include "df-div.mm"
include "riotaex.mm"
include "fnmpt2i.mm"
include "zsscn.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "xpss12.mm"
include "mp2an.mm"
include "ovelimab.mm"
include "bitri.mm"

theorem elq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( A e. QQ <-> E. x e. ZZ E. y e. NN A = ( x / y ) )

  proof
    cA
    cq
    wcel
    cA
    cdiv
    cz
    cn
    cxp
    #
    cima
    #
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    wceq
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    cq
    @1
    cA
    df-q
    eleq2i
    cdiv
    cc
    cc
    cc0
    csn
    cdif
    #
    cxp
    #
    wfn
    @0
    @7
    wss
    #
    @2
    @5
    wb
    vx
    vy
    cc
    @6
    @4
    vz
    cv
    cmul
    co
    @3
    wceq
    #
    vz
    cc
    crio
    cdiv
    vx
    vy
    vz
    df-div
    @9
    vz
    cc
    riotaex
    fnmpt2i
    cz
    cc
    wss
    cn
    @6
    wss
    @8
    zsscn
    vx
    cn
    @6
    @3
    cn
    wcel
    @3
    cc
    wcel
    @3
    cc0
    wne
    @3
    @6
    wcel
    @3
    nncn
    @3
    nnne0
    @3
    cc
    cc0
    eldifsn
    sylanbrc
    ssriv
    cz
    cc
    cn
    @6
    xpss12
    mp2an
    vx
    vy
    @7
    cz
    cn
    cA
    cdiv
    ovelimab
    mp2an
    bitri
end
