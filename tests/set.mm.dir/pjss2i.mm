include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "choccli.mm"
include "pjclii.mm"
include "chsscon3i.mm"
include "ssel.mm"
include "mpi.mm"
include "sylbi.mm"
include "csh.mm"
include "chshii.mm"
include "shsubcl.mm"
include "mp3an1.mm"
include "sylancr.mm"
include "c0v.mm"
include "pjsslem.mm"
include "eleq1i.mm"
include "pjhclii.mm"
include "hvsubcli.mm"
include "pjoc2i.mm"
include "bitri.mm"
include "pjsubii.mm"
include "eqeq1i.mm"
include "hvsubeq0i.mm"
include "pjidmi.mm"
include "eqeq2i.mm"
include "3bitrri.mm"
include "sylibr.mm"

theorem pjss2i
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( H C_ G -> ( ( projh ` H ) ` ( ( projh ` G ) ` A ) ) = ( ( projh ` H ) ` A ) )

  proof
    cH
    cG
    wss
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cA
    cG
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    @1
    wcel
    #
    cA
    cG
    cpjh
    cfv
    cfv
    #
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    @8
    cfv
    #
    wceq
    #
    @0
    @2
    @1
    wcel
    #
    @4
    @1
    wcel
    #
    @6
    cA
    @1
    cH
    pjidm.1
    choccli
    #
    pjidm.2
    pjclii
    @0
    @3
    @1
    wss
    #
    @13
    cH
    cG
    pjidm.1
    pjsslem.1
    chsscon3i
    @15
    @4
    @3
    wcel
    @13
    cA
    @3
    cG
    pjsslem.1
    choccli
    pjidm.2
    pjclii
    @3
    @1
    @4
    ssel
    mpi
    sylbi
    @1
    csh
    wcel
    @12
    @13
    @6
    @1
    @14
    chshii
    @2
    @4
    @1
    shsubcl
    mp3an1
    sylancr
    @6
    @7
    @10
    cmv
    co
    #
    @8
    cfv
    #
    c0v
    wceq
    #
    @9
    @10
    @8
    cfv
    #
    wceq
    #
    @11
    @6
    @16
    @1
    wcel
    @18
    @5
    @16
    @1
    cA
    cG
    cH
    pjidm.1
    pjidm.2
    pjsslem.1
    pjsslem
    eleq1i
    @16
    cH
    pjidm.1
    @7
    @10
    cA
    cG
    pjsslem.1
    pjidm.2
    pjhclii
    #
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    hvsubcli
    pjoc2i
    bitri
    @18
    @9
    @19
    cmv
    co
    #
    c0v
    wceq
    @20
    @17
    @23
    c0v
    @7
    @10
    cH
    pjidm.1
    @21
    @22
    pjsubii
    eqeq1i
    @9
    @19
    @7
    cH
    pjidm.1
    @21
    pjhclii
    @10
    cH
    pjidm.1
    @22
    pjhclii
    hvsubeq0i
    bitri
    @19
    @10
    @9
    cA
    cH
    pjidm.1
    pjidm.2
    pjidmi
    eqeq2i
    3bitrri
    sylibr
end
