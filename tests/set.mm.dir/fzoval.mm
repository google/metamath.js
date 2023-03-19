include "cz.mm"
include "wcel.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wceq.mm"
include "cv.mm"
include "id.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "df-fzo.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "wa.mm"
include "simpl.mm"
include "con3i.mm"
include "cxp.mm"
include "cpw.mm"
include "fzof.mm"
include "fdmi.mm"
include "ndmov.mm"
include "syl.mm"
include "fzf.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem fzoval
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n


  assert |- ( N e. ZZ -> ( M ..^ N ) = ( M ... ( N - 1 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cfzo
    co
    #
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wceq
    #
    vm
    vn
    cM
    cN
    cz
    cz
    vm
    cv
    #
    vn
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    @4
    cfzo
    @6
    cM
    wceq
    #
    @7
    cN
    wceq
    @6
    cM
    @8
    @3
    cfz
    @9
    id
    @7
    cN
    c1
    cmin
    oveq1
    oveqan12d
    vm
    vn
    df-fzo
    cM
    @3
    cfz
    ovex
    ovmpt2a
    @0
    wn
    #
    @5
    @1
    @10
    @2
    c0
    @4
    @10
    @0
    @1
    wa
    #
    wn
    @2
    c0
    wceq
    @11
    @0
    @0
    @1
    simpl
    con3i
    cM
    cN
    cz
    cfzo
    cz
    cz
    cxp
    #
    cz
    cpw
    #
    cfzo
    fzof
    fdmi
    ndmov
    syl
    @10
    @0
    @3
    cz
    wcel
    #
    wa
    #
    wn
    @4
    c0
    wceq
    @15
    @0
    @0
    @14
    simpl
    con3i
    cM
    @3
    cz
    cfz
    @12
    @13
    cfz
    fzf
    fdmi
    ndmov
    syl
    eqtr4d
    adantr
    pm2.61ian
end
