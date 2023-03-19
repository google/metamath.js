include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "csuc.mm"
include "wcel.mm"
include "ciun.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "csn.mm"
include "cdif.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1145.mm"

theorem bnj1147
  let cA: class A
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y


  assert |- _trCl ( X , A , R ) C_ A

  proof
    c0
    vf
    cv
    #
    cfv
    cA
    cR
    cX
    c-bnj14
    wceq
    #
    vi
    cv
    #
    csuc
    #
    vn
    cv
    #
    wcel
    @3
    @0
    cfv
    vy
    @2
    @0
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    @4
    com
    c0
    csn
    cdif
    #
    wcel
    @0
    @4
    wfn
    #
    @1
    @5
    w-bnj17
    #
    @2
    c0
    wne
    @2
    @4
    wcel
    @8
    w3a
    vj
    cv
    #
    @4
    wcel
    @2
    @9
    csuc
    wceq
    wa
    wa
    #
    vy
    cA
    @7
    @1
    @5
    w3a
    vn
    @6
    wrex
    vf
    cab
    #
    @6
    cR
    vf
    vi
    vj
    vn
    cX
    @1
    biid
    @5
    biid
    @6
    eqid
    @11
    eqid
    @8
    biid
    @10
    biid
    bnj1145
end
