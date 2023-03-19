include "c1.mm"
include "cvv.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cn.mm"
include "c0.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "1ex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "wfn.mm"
include "frfnom.mm"
include "peano1.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "cima.mm"
include "df-nn.mm"
include "df-ima.mm"
include "eqtri.mm"
include "eleqtrri.mm"

theorem 1nn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A


  assert |- 1 e. NN

  proof
    c1
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    c1
    crdg
    #
    com
    cres
    #
    crn
    #
    cn
    c0
    @2
    cfv
    #
    c1
    @3
    c1
    cvv
    wcel
    @4
    c1
    wceq
    1ex
    c1
    cvv
    @0
    fr0g
    ax-mp
    @2
    com
    wfn
    c0
    com
    wcel
    @4
    @3
    wcel
    c1
    @0
    frfnom
    peano1
    com
    c0
    @2
    fnfvelrn
    mp2an
    eqeltrri
    cn
    @1
    com
    cima
    @3
    vx
    df-nn
    @1
    com
    df-ima
    eqtri
    eleqtrri
end
