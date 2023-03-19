include "cva.mm"
include "co.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "pjpji.mm"
include "oveq12i.mm"
include "pjhclii.mm"
include "choccli.mm"
include "hvadd4i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "wcel.mm"
include "wceq.mm"
include "csh.mm"
include "chshii.mm"
include "pjclii.mm"
include "shaddcl.mm"
include "mp3an.mm"
include "pjcompi.mm"
include "mp2an.mm"

theorem pjaddii
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjadj.3: |- B e. ~H


  assert |- ( ( projh ` H ) ` ( A +h B ) ) = ( ( ( projh ` H ) ` A ) +h ( ( projh ` H ) ` B ) )

  proof
    cA
    cB
    cva
    co
    #
    cH
    cpjh
    cfv
    #
    cfv
    cA
    @1
    cfv
    #
    cB
    @1
    cfv
    #
    cva
    co
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    cB
    @6
    cfv
    #
    cva
    co
    #
    cva
    co
    #
    @1
    cfv
    #
    @4
    @0
    @10
    @1
    @0
    @2
    @7
    cva
    co
    #
    @3
    @8
    cva
    co
    #
    cva
    co
    @10
    cA
    @12
    cB
    @13
    cva
    cA
    cH
    pjidm.1
    pjidm.2
    pjpji
    cB
    cH
    pjidm.1
    pjadj.3
    pjpji
    oveq12i
    @2
    @7
    @3
    @8
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    cA
    @5
    cH
    pjidm.1
    choccli
    #
    pjidm.2
    pjhclii
    cB
    cH
    pjidm.1
    pjadj.3
    pjhclii
    cB
    @5
    @14
    pjadj.3
    pjhclii
    hvadd4i
    eqtri
    fveq2i
    @4
    cH
    wcel
    #
    @9
    @5
    wcel
    #
    @11
    @4
    wceq
    cH
    csh
    wcel
    @2
    cH
    wcel
    @3
    cH
    wcel
    @15
    cH
    pjidm.1
    chshii
    cA
    cH
    pjidm.1
    pjidm.2
    pjclii
    cB
    cH
    pjidm.1
    pjadj.3
    pjclii
    @2
    @3
    cH
    shaddcl
    mp3an
    @5
    csh
    wcel
    @7
    @5
    wcel
    @8
    @5
    wcel
    @16
    @5
    @14
    chshii
    cA
    @5
    @14
    pjidm.2
    pjclii
    cB
    @5
    @14
    pjadj.3
    pjclii
    @7
    @8
    @5
    shaddcl
    mp3an
    @4
    @9
    cH
    pjidm.1
    pjcompi
    mp2an
    eqtri
end
