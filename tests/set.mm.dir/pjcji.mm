include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cpjh.mm"
include "cva.mm"
include "co.mm"
include "chj.mm"
include "cmv.mm"
include "cin.mm"
include "choccli.mm"
include "pjssmii.mm"
include "oveq2d.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "pjpoi.mm"
include "oveq2i.mm"
include "pjhclii.mm"
include "hvnegdii.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "hvaddsub12.mm"
include "mp3an.mm"
include "eqtr4i.mm"
include "hvsubcli.mm"
include "hvsubvali.mm"
include "chjcomi.mm"
include "chdmm4i.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "chincli.mm"
include "pjopi.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "eqcomd.mm"

theorem pjcji
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( H C_ ( _|_ ` G ) -> ( ( projh ` ( H vH G ) ) ` A ) = ( ( ( projh ` H ) ` A ) +h ( ( projh ` G ) ` A ) ) )

  proof
    cH
    cG
    cort
    cfv
    #
    wss
    #
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
    cva
    co
    #
    cA
    cH
    cG
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    @1
    cA
    cA
    @0
    cpjh
    cfv
    cfv
    #
    @2
    cmv
    co
    #
    cmv
    co
    #
    cA
    cA
    @0
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
    cmv
    co
    #
    @4
    @7
    @1
    @9
    @13
    cA
    cmv
    cA
    @0
    cH
    pjidm.1
    pjidm.2
    cG
    pjsslem.1
    choccli
    #
    pjssmii
    oveq2d
    @4
    cA
    c1
    cneg
    @9
    csm
    co
    #
    cva
    co
    #
    @10
    @4
    @2
    cA
    @8
    cmv
    co
    #
    cva
    co
    #
    @17
    @3
    @18
    @2
    cva
    cA
    cG
    pjsslem.1
    pjidm.2
    pjpoi
    oveq2i
    @17
    cA
    @2
    @8
    cmv
    co
    #
    cva
    co
    #
    @19
    @16
    @20
    cA
    cva
    @8
    @2
    cA
    @0
    @15
    pjidm.2
    pjhclii
    #
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    hvnegdii
    oveq2i
    @2
    chil
    wcel
    cA
    chil
    wcel
    @8
    chil
    wcel
    @19
    @21
    wceq
    @23
    pjidm.2
    @22
    @2
    cA
    @8
    hvaddsub12
    mp3an
    eqtr4i
    eqtr4i
    cA
    @9
    pjidm.2
    @8
    @2
    @22
    @23
    hvsubcli
    hvsubvali
    eqtr4i
    @7
    cA
    @12
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    @14
    cA
    @6
    @25
    @5
    @24
    cpjh
    @5
    cG
    cH
    chj
    co
    @24
    cH
    cG
    pjidm.1
    pjsslem.1
    chjcomi
    cG
    cH
    pjsslem.1
    pjidm.1
    chdmm4i
    eqtr4i
    fveq2i
    fveq1i
    cA
    @12
    @0
    @11
    @15
    cH
    pjidm.1
    choccli
    chincli
    pjidm.2
    pjopi
    eqtri
    3eqtr4g
    eqcomd
end
