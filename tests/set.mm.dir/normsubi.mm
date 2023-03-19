include "c1.mm"
include "cneg.mm"
include "cmv.mm"
include "co.mm"
include "csm.mm"
include "cno.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "neg1cn.mm"
include "hvsubcli.mm"
include "norm-iii-i.mm"
include "hvnegdii.mm"
include "fveq2i.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "normcli.mm"
include "recni.mm"
include "mulid2i.mm"
include "3eqtr3i.mm"

theorem normsubi
  let cA: class A
  let cB: class B
  assume normsub.1: |- A e. ~H
  assume normsub.2: |- B e. ~H


  assert |- ( normh ` ( A -h B ) ) = ( normh ` ( B -h A ) )

  proof
    c1
    cneg
    #
    cB
    cA
    cmv
    co
    #
    csm
    co
    #
    cno
    cfv
    @0
    cabs
    cfv
    #
    @1
    cno
    cfv
    #
    cmul
    co
    #
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    @4
    @0
    @1
    neg1cn
    cB
    cA
    normsub.2
    normsub.1
    hvsubcli
    #
    norm-iii-i
    @2
    @6
    cno
    cB
    cA
    normsub.2
    normsub.1
    hvnegdii
    fveq2i
    @5
    c1
    @4
    cmul
    co
    @4
    @3
    c1
    @4
    cmul
    @3
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    @4
    @4
    @1
    @7
    normcli
    recni
    mulid2i
    eqtri
    3eqtr3i
end
