include "clmod.mm"
include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "clspn.mm"
include "cbs.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "linds1.mm"
include "a1i.mm"
include "eqid.mm"
include "ressbasss.mm"
include "syl6ss.mm"
include "adantr.mm"
include "wb.mm"
include "clss.mm"
include "simpl.mm"
include "lspcl.mm"
include "lspssid.mm"
include "lsslsp.mm"
include "syl3anc.mm"
include "lspssv.mm"
include "ressbas2.mm"
include "syl.mm"
include "eqtr3d.mm"
include "biantrud.mm"
include "lsslinds.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "islbs4.mm"
include "syl6bbr.mm"

theorem islinds3
  let cB: class B
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume islinds3.b: |- B = ( Base ` W )
  assume islinds3.k: |- K = ( LSpan ` W )
  assume islinds3.x: |- X = ( W |`s ( K ` Y ) )
  assume islinds3.j: |- J = ( LBasis ` X )


  assert |- ( W e. LMod -> ( Y e. ( LIndS ` W ) <-> Y e. J ) )

  proof
    cW
    clmod
    wcel
    #
    cY
    cW
    clinds
    cfv
    wcel
    #
    cY
    cX
    clinds
    cfv
    wcel
    #
    cY
    cX
    clspn
    cfv
    #
    cfv
    #
    cX
    cbs
    cfv
    #
    wceq
    #
    wa
    #
    cY
    cJ
    wcel
    @0
    cY
    cB
    wss
    #
    @1
    @7
    @1
    @8
    wi
    @0
    cB
    cW
    cY
    islinds3.b
    linds1
    a1i
    @7
    @8
    wi
    @0
    @2
    @8
    @6
    @2
    cY
    @5
    cB
    @5
    cX
    cY
    @5
    eqid
    #
    linds1
    cY
    cK
    cfv
    #
    cB
    cX
    cW
    islinds3.x
    islinds3.b
    ressbasss
    syl6ss
    adantr
    a1i
    @0
    @8
    @1
    @7
    wb
    @0
    @8
    wa
    #
    @1
    @1
    @6
    wa
    @7
    @11
    @6
    @1
    @11
    @10
    @4
    @5
    @11
    @0
    @10
    cW
    clss
    cfv
    #
    wcel
    #
    cY
    @10
    wss
    #
    @10
    @4
    wceq
    @0
    @8
    simpl
    #
    @12
    cY
    cK
    cB
    cW
    islinds3.b
    @12
    eqid
    #
    islinds3.k
    lspcl
    #
    cY
    cK
    cB
    cW
    islinds3.b
    islinds3.k
    lspssid
    #
    @10
    cY
    @12
    cK
    @3
    cW
    cX
    islinds3.x
    islinds3.k
    @3
    eqid
    #
    @16
    lsslsp
    syl3anc
    @11
    @10
    cB
    wss
    @10
    @5
    wceq
    cY
    cK
    cB
    cW
    islinds3.b
    islinds3.k
    lspssv
    @10
    cB
    cX
    cW
    islinds3.x
    islinds3.b
    ressbas2
    syl
    eqtr3d
    biantrud
    @11
    @1
    @2
    @6
    @11
    @2
    @1
    @11
    @0
    @13
    @14
    @2
    @1
    wb
    @15
    @17
    @18
    @10
    @12
    cY
    cW
    cX
    @16
    islinds3.x
    lsslinds
    syl3anc
    bicomd
    anbi1d
    bitrd
    ex
    pm5.21ndd
    @5
    cJ
    @3
    cX
    cY
    @9
    islinds3.j
    @19
    islbs4
    syl6bbr
end
