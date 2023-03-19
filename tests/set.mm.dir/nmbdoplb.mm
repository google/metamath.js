include "cbo.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "cno.mm"
include "cnop.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "ch0o.mm"
include "cif.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "0bdop.mm"
include "elimel.mm"
include "nmbdoplbi.mm"
include "dedth.mm"
include "imp.mm"

theorem nmbdoplb
  let cA: class A
  let cT: class T


  assert |- ( ( T e. BndLinOp /\ A e. ~H ) -> ( normh ` ( T ` A ) ) <_ ( ( normop ` T ) x. ( normh ` A ) ) )

  proof
    cT
    cbo
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cno
    cfv
    #
    cT
    cnop
    cfv
    #
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    @7
    wi
    @1
    cA
    @0
    cT
    ch0o
    cif
    #
    cfv
    #
    cno
    cfv
    #
    @8
    cnop
    cfv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    #
    wi
    cT
    ch0o
    cT
    @8
    wceq
    #
    @7
    @13
    @1
    @14
    @3
    @10
    @6
    @12
    cle
    @14
    @2
    @9
    cno
    cA
    cT
    @8
    fveq1
    fveq2d
    @14
    @4
    @11
    @5
    cmul
    cT
    @8
    cnop
    fveq2
    oveq1d
    breq12d
    imbi2d
    cA
    @8
    cT
    ch0o
    cbo
    0bdop
    elimel
    nmbdoplbi
    dedth
    imp
end
