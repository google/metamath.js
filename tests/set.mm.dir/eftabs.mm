include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cabs.mm"
include "expcl.mm"
include "cn.mm"
include "faccl.mm"
include "adantl.mm"
include "nncnd.mm"
include "cc0.mm"
include "wne.mm"
include "facne0.mm"
include "absdivd.mm"
include "absexp.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem eftabs
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. NN0 ) -> ( abs ` ( ( A ^ K ) / ( ! ` K ) ) ) = ( ( ( abs ` A ) ^ K ) / ( ! ` K ) ) )

  proof
    cA
    cc
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cA
    cK
    cexp
    co
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    cabs
    cfv
    @3
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    cdiv
    co
    cA
    cabs
    cfv
    cK
    cexp
    co
    #
    @4
    cdiv
    co
    @2
    @3
    @4
    cA
    cK
    expcl
    @2
    @4
    @1
    @4
    cn
    wcel
    @0
    cK
    faccl
    adantl
    #
    nncnd
    @1
    @4
    cc0
    wne
    @0
    cK
    facne0
    adantl
    absdivd
    @2
    @5
    @7
    @6
    @4
    cdiv
    cA
    cK
    absexp
    @2
    @4
    @2
    @4
    @8
    nnred
    @2
    @4
    @2
    @4
    @8
    nnnn0d
    nn0ge0d
    absidd
    oveq12d
    eqtrd
end
