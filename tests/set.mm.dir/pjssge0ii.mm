include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "cc0.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "csp.mm"
include "cle.mm"
include "choccli.mm"
include "chincli.mm"
include "pjhclii.mm"
include "normcli.mm"
include "sqge0i.mm"
include "oveq1.mm"
include "pjinormii.mm"
include "syl6eq.mm"
include "syl5breqr.mm"

theorem pjssge0ii
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) = ( ( projh ` ( G i^i ( _|_ ` H ) ) ) ` A ) -> 0 <_ ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) .ih A ) )

  proof
    cA
    cG
    cpjh
    cfv
    cfv
    cA
    cH
    cpjh
    cfv
    cfv
    cmv
    co
    #
    cA
    cG
    cH
    cort
    cfv
    #
    cin
    #
    cpjh
    cfv
    cfv
    #
    wceq
    #
    cc0
    @3
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @0
    cA
    csp
    co
    #
    cle
    @5
    @3
    cA
    @2
    cG
    @1
    pjsslem.1
    cH
    pjidm.1
    choccli
    chincli
    #
    pjidm.2
    pjhclii
    normcli
    sqge0i
    @4
    @7
    @3
    cA
    csp
    co
    @6
    @0
    @3
    cA
    csp
    oveq1
    cA
    @2
    @8
    pjidm.2
    pjinormii
    syl6eq
    syl5breqr
end
