include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "breq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "c1.mm"
include "cfzo.mm"
include "wi.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "cuz.mm"
include "wss.mm"
include "cz.mm"
include "cn0.mm"
include "elfzoel2.mm"
include "elfzonn0.mm"
include "eluzmn.mm"
include "syl2anc.mm"
include "fzss2.mm"
include "syl.mm"
include "sseld.mm"
include "3syl.mm"
include "imp.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmptd.mm"
include "elfzle2.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem crctcshwlkn0lem2
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cJ: class J
  let cN: class N
  assume crctcshwlkn0lem.s: |- ( ph -> S e. ( 1 ..^ N ) )
  assume crctcshwlkn0lem.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint J x
  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  assert |- ( ( ph /\ J e. ( 0 ... ( N - S ) ) ) -> ( Q ` J ) = ( P ` ( J + S ) ) )

  proof
    wph
    cJ
    cc0
    cN
    cS
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cJ
    cQ
    cfv
    cJ
    @0
    cle
    wbr
    #
    cJ
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @5
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    @6
    @3
    vx
    cJ
    vx
    cv
    #
    @0
    cle
    wbr
    #
    @10
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @12
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    @9
    cc0
    cN
    cfz
    co
    #
    cQ
    cvv
    cQ
    vx
    @17
    @16
    cmpt
    wceq
    @3
    crctcshwlkn0lem.q
    a1i
    @10
    cJ
    wceq
    #
    @16
    @9
    wceq
    @3
    @18
    @11
    @4
    @13
    @15
    @6
    @8
    @10
    cJ
    @0
    cle
    breq1
    @18
    @12
    @5
    cP
    @10
    cJ
    cS
    caddc
    oveq1
    #
    fveq2d
    @18
    @14
    @7
    cP
    @18
    @12
    @5
    cN
    cmin
    @19
    oveq1d
    fveq2d
    ifbieq12d
    adantl
    wph
    @2
    cJ
    @17
    wcel
    #
    wph
    cS
    c1
    cN
    cfzo
    co
    #
    wcel
    cS
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @2
    @20
    wi
    crctcshwlkn0lem.s
    @21
    @22
    cS
    cN
    fzo0ss1
    sseli
    @23
    @1
    @17
    cJ
    @23
    cN
    @0
    cuz
    cfv
    wcel
    #
    @1
    @17
    wss
    @23
    cN
    cz
    wcel
    cS
    cn0
    wcel
    @24
    cS
    cc0
    cN
    elfzoel2
    cS
    cN
    elfzonn0
    cN
    cS
    eluzmn
    syl2anc
    @0
    cc0
    cN
    fzss2
    syl
    sseld
    3syl
    imp
    @9
    cvv
    wcel
    @3
    @4
    @6
    @8
    @5
    cP
    fvex
    @7
    cP
    fvex
    ifex
    a1i
    fvmptd
    @3
    @4
    @6
    @8
    @2
    @4
    wph
    cJ
    cc0
    @0
    elfzle2
    adantl
    iftrued
    eqtrd
end
