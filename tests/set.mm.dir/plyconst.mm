include "cc.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cply.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "exp0.mm"
include "adantl.mm"
include "oveq2d.mm"
include "ssel2.mm"
include "adantr.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "cn0.mm"
include "0nn0.mm"
include "eqid.mm"
include "ply1term.mm"
include "mp3an3.mm"
include "eqeltrrd.mm"

theorem plyconst
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let cN: class N
  let wph: wff ph


  assert |- ( ( S C_ CC /\ A e. S ) -> ( CC X. { A } ) e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    cA
    cS
    wcel
    #
    wa
    #
    vz
    cc
    cA
    vz
    cv
    #
    cc0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc
    cA
    csn
    cxp
    #
    cS
    cply
    cfv
    #
    @2
    @6
    vz
    cc
    cA
    cmpt
    @7
    @2
    vz
    cc
    @5
    cA
    @2
    @3
    cc
    wcel
    #
    wa
    #
    @5
    cA
    c1
    cmul
    co
    cA
    @10
    @4
    c1
    cA
    cmul
    @9
    @4
    c1
    wceq
    @2
    @3
    exp0
    adantl
    oveq2d
    @10
    cA
    @2
    cA
    cc
    wcel
    @9
    cS
    cc
    cA
    ssel2
    adantr
    mulid1d
    eqtrd
    mpteq2dva
    vz
    cc
    cA
    fconstmpt
    syl6eqr
    @0
    @1
    cc0
    cn0
    wcel
    @6
    @8
    wcel
    0nn0
    vz
    cA
    cS
    @6
    cc0
    @6
    eqid
    ply1term
    mp3an3
    eqeltrrd
end
