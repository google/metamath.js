include "chil.mm"
include "wcel.mm"
include "cc0.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "cno.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "id.mm"
include "breq2d.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "bibi12d.mm"
include "ifhvhv0.mm"
include "pjdifnormii.mm"
include "dedth.mm"

theorem pjdifnormi
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( A e. ~H -> ( 0 <_ ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) .ih A ) <-> ( normh ` ( ( projh ` H ) ` A ) ) <_ ( normh ` ( ( projh ` G ) ` A ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cc0
    cA
    cG
    cpjh
    cfv
    #
    cfv
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cmv
    co
    #
    cA
    csp
    co
    #
    cle
    wbr
    #
    @4
    cno
    cfv
    #
    @2
    cno
    cfv
    #
    cle
    wbr
    #
    wb
    cc0
    @0
    cA
    c0v
    cif
    #
    @1
    cfv
    #
    @11
    @3
    cfv
    #
    cmv
    co
    #
    @11
    csp
    co
    #
    cle
    wbr
    #
    @13
    cno
    cfv
    #
    @12
    cno
    cfv
    #
    cle
    wbr
    #
    wb
    cA
    c0v
    cA
    @11
    wceq
    #
    @7
    @16
    @10
    @19
    @20
    @6
    @15
    cc0
    cle
    @20
    @5
    @14
    cA
    @11
    csp
    @20
    @2
    @12
    @4
    @13
    cmv
    cA
    @11
    @1
    fveq2
    #
    cA
    @11
    @3
    fveq2
    #
    oveq12d
    @20
    id
    oveq12d
    breq2d
    @20
    @8
    @17
    @9
    @18
    cle
    @20
    @4
    @13
    cno
    @22
    fveq2d
    @20
    @2
    @12
    cno
    @21
    fveq2d
    breq12d
    bibi12d
    @11
    cG
    cH
    pjco.2
    cA
    ifhvhv0
    pjco.1
    pjdifnormii
    dedth
end
