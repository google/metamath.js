include "csm.mm"
include "co.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "cva.mm"
include "pjpji.mm"
include "oveq2i.mm"
include "pjhclii.mm"
include "choccli.mm"
include "hvdistr1i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "wcel.mm"
include "wceq.mm"
include "csh.mm"
include "cc.mm"
include "chshii.mm"
include "pjclii.mm"
include "shmulcl.mm"
include "mp3an.mm"
include "pjcompi.mm"
include "mp2an.mm"

theorem pjmulii
  let cA: class A
  let cC: class C
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjmul.3: |- C e. CC


  assert |- ( ( projh ` H ) ` ( C .h A ) ) = ( C .h ( ( projh ` H ) ` A ) )

  proof
    cC
    cA
    csm
    co
    #
    cH
    cpjh
    cfv
    #
    cfv
    cC
    cA
    @1
    cfv
    #
    csm
    co
    #
    cC
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    csm
    co
    #
    cva
    co
    #
    @1
    cfv
    #
    @3
    @0
    @7
    @1
    @0
    cC
    @2
    @5
    cva
    co
    #
    csm
    co
    @7
    cA
    @9
    cC
    csm
    cA
    cH
    pjidm.1
    pjidm.2
    pjpji
    oveq2i
    cC
    @2
    @5
    pjmul.3
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    cA
    @4
    cH
    pjidm.1
    choccli
    #
    pjidm.2
    pjhclii
    hvdistr1i
    eqtri
    fveq2i
    @3
    cH
    wcel
    #
    @6
    @4
    wcel
    #
    @8
    @3
    wceq
    cH
    csh
    wcel
    cC
    cc
    wcel
    #
    @2
    cH
    wcel
    @11
    cH
    pjidm.1
    chshii
    pjmul.3
    cA
    cH
    pjidm.1
    pjidm.2
    pjclii
    cC
    @2
    cH
    shmulcl
    mp3an
    @4
    csh
    wcel
    @13
    @5
    @4
    wcel
    @12
    @4
    @10
    chshii
    pjmul.3
    cA
    @4
    @10
    pjidm.2
    pjclii
    cC
    @5
    @4
    shmulcl
    mp3an
    @3
    @6
    cH
    pjidm.1
    pjcompi
    mp2an
    eqtri
end
