include "ccm.mm"
include "wbr.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "pjclem2.mm"
include "cin.mm"
include "cort.mm"
include "chj.mm"
include "co.mm"
include "chos.mm"
include "pjclem4.mm"
include "pjclem3.mm"
include "choccli.mm"
include "syl.mm"
include "oveq12d.mm"
include "chil.mm"
include "chio.mm"
include "df-iop.mm"
include "coeq2i.mm"
include "pjfi.mm"
include "hoid1i.mm"
include "eqtr3i.mm"
include "pjtoi.mm"
include "pjsdii.mm"
include "wss.mm"
include "inss2.mm"
include "chub2i.mm"
include "sstri.mm"
include "chdmm3i.mm"
include "sseqtr4i.mm"
include "chincli.mm"
include "pjscji.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "chjcli.mm"
include "pj11i.mm"
include "sylib.mm"
include "cmbri.mm"
include "sylibr.mm"
include "impbii.mm"

theorem pjci
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( G C_H H <-> ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) )

  proof
    cG
    cH
    ccm
    wbr
    #
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @2
    @1
    ccom
    wceq
    #
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem2
    @4
    cG
    cG
    cH
    cin
    #
    cG
    cH
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    #
    @0
    @4
    @1
    @8
    cpjh
    cfv
    #
    wceq
    @9
    @4
    @3
    @1
    @6
    cpjh
    cfv
    #
    ccom
    #
    chos
    co
    #
    @5
    cpjh
    cfv
    #
    @7
    cpjh
    cfv
    #
    chos
    co
    #
    @1
    @10
    @4
    @3
    @14
    @12
    @15
    chos
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem4
    @4
    @12
    @11
    @1
    ccom
    wceq
    @12
    @15
    wceq
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem3
    cG
    @6
    pjclem1.1
    cH
    pjclem1.2
    choccli
    #
    pjclem4
    syl
    oveq12d
    @1
    chil
    cpjh
    cfv
    #
    ccom
    #
    @1
    @13
    @1
    chio
    ccom
    @19
    @1
    chio
    @18
    @1
    df-iop
    coeq2i
    @1
    cG
    pjclem1.1
    pjfi
    hoid1i
    eqtr3i
    @1
    @2
    @11
    chos
    co
    #
    ccom
    @19
    @13
    @20
    @18
    @1
    cH
    pjclem1.2
    pjtoi
    coeq2i
    @2
    @11
    cG
    pjclem1.1
    cH
    pjclem1.2
    pjfi
    @6
    @17
    pjfi
    pjsdii
    eqtr3i
    eqtr3i
    @5
    @7
    cort
    cfv
    #
    wss
    @10
    @16
    wceq
    @5
    cG
    cort
    cfv
    #
    cH
    chj
    co
    #
    @21
    @5
    cH
    @23
    cG
    cH
    inss2
    cH
    @22
    pjclem1.2
    cG
    pjclem1.1
    choccli
    chub2i
    sstri
    cG
    cH
    pjclem1.1
    pjclem1.2
    chdmm3i
    sseqtr4i
    @5
    @7
    cG
    cH
    pjclem1.1
    pjclem1.2
    chincli
    #
    cG
    @6
    pjclem1.1
    @17
    chincli
    #
    pjscji
    ax-mp
    3eqtr4g
    cG
    @8
    pjclem1.1
    @5
    @7
    @24
    @25
    chjcli
    pj11i
    sylib
    cG
    cH
    pjclem1.1
    pjclem1.2
    cmbri
    sylibr
    impbii
end
