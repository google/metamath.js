include "cc.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "c0p.mm"
include "wceq.mm"
include "0pval.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "imp.mm"

theorem ne0p
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let cN: class N
  let wph: wff ph
  let cS: class S


  assert |- ( ( A e. CC /\ ( F ` A ) =/= 0 ) -> F =/= 0p )

  proof
    cA
    cc
    wcel
    #
    cA
    cF
    cfv
    #
    cc0
    wne
    cF
    c0p
    wne
    @0
    cF
    c0p
    @1
    cc0
    @0
    @1
    cc0
    wceq
    cF
    c0p
    wceq
    #
    cA
    c0p
    cfv
    #
    cc0
    wceq
    cA
    0pval
    @2
    @1
    @3
    cc0
    cA
    cF
    c0p
    fveq1
    eqeq1d
    syl5ibrcom
    necon3d
    imp
end
