include "cword.mm"
include "wcel.mm"
include "cpfx.mm"
include "co.mm"
include "c0.mm"
include "eleq1.mm"
include "wne.mm"
include "cn0.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wi.mm"
include "cvv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "df-pfx.mm"
include "elmpt2cl2.mm"
include "idi.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "wa.mm"
include "pfxval.mm"
include "swrdcl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "wrd0.mm"
include "a1i.mm"
include "pm2.61ne.mm"

theorem pfxcl
  let cA: class A
  let cS: class S
  let cL: class L
  let vx: setvar x
  let vl: setvar l
  let vs: setvar s
  let vk: setvar k


  assert |- ( S e. Word A -> ( S prefix L ) e. Word A )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cS
    cL
    cpfx
    co
    #
    @0
    wcel
    #
    c0
    @0
    wcel
    #
    @2
    c0
    @2
    c0
    @0
    eleq1
    @2
    c0
    wne
    #
    @1
    cL
    cn0
    wcel
    #
    @3
    @5
    vx
    cv
    #
    @2
    wcel
    #
    vx
    wex
    @6
    vx
    @2
    n0
    @8
    @6
    vx
    @8
    @6
    wi
    vs
    vl
    cvv
    cn0
    vs
    cv
    cc0
    vl
    cv
    cop
    csubstr
    co
    cS
    cL
    cpfx
    @7
    vs
    vl
    df-pfx
    elmpt2cl2
    idi
    exlimiv
    sylbi
    @1
    @6
    wa
    @2
    cS
    cc0
    cL
    cop
    csubstr
    co
    #
    @0
    cS
    cL
    @0
    pfxval
    @1
    @9
    @0
    wcel
    @6
    cA
    cS
    cc0
    cL
    swrdcl
    adantr
    eqeltrd
    sylan2
    @4
    @1
    cA
    wrd0
    a1i
    pm2.61ne
end
