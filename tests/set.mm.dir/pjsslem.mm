include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "chil.mm"
include "cch.mm"
include "wcel.mm"
include "wceq.mm"
include "pjo.mm"
include "mp2an.mm"
include "oveq12i.mm"
include "helch.mm"
include "pjclii.mm"
include "pjhclii.mm"
include "hvsubsub4i.mm"
include "hvsubid.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "3eqtri.mm"
include "hvsubcli.mm"
include "hv2negi.mm"
include "hvnegdii.mm"

theorem pjsslem
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( ( ( projh ` ( _|_ ` H ) ) ` A ) -h ( ( projh ` ( _|_ ` G ) ) ` A ) ) = ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) )

  proof
    cA
    cH
    cort
    cfv
    cpjh
    cfv
    cfv
    #
    cA
    cG
    cort
    cfv
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    c0v
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cA
    cG
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    cmv
    co
    #
    c1
    cneg
    @5
    csm
    co
    @4
    @3
    cmv
    co
    @2
    cA
    chil
    cpjh
    cfv
    cfv
    #
    @3
    cmv
    co
    #
    @7
    @4
    cmv
    co
    #
    cmv
    co
    @7
    @7
    cmv
    co
    #
    @5
    cmv
    co
    @6
    @0
    @8
    @1
    @9
    cmv
    cH
    cch
    wcel
    cA
    chil
    wcel
    #
    @0
    @8
    wceq
    pjidm.1
    pjidm.2
    cA
    cH
    pjo
    mp2an
    cG
    cch
    wcel
    @11
    @1
    @9
    wceq
    pjsslem.1
    pjidm.2
    cA
    cG
    pjo
    mp2an
    oveq12i
    @7
    @3
    @7
    @4
    cA
    chil
    helch
    pjidm.2
    pjclii
    #
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    @12
    cA
    cG
    pjsslem.1
    pjidm.2
    pjhclii
    #
    hvsubsub4i
    @10
    c0v
    @5
    cmv
    @7
    chil
    wcel
    @10
    c0v
    wceq
    @12
    @7
    hvsubid
    ax-mp
    oveq1i
    3eqtri
    @5
    @3
    @4
    @13
    @14
    hvsubcli
    hv2negi
    @3
    @4
    @13
    @14
    hvnegdii
    3eqtri
end
