include "co.mm"
include "wbr.mm"
include "ccnv.mm"
include "wa.mm"
include "cin.mm"
include "invfval.mm"
include "breqd.mm"
include "brin.mm"
include "syl6bb.mm"
include "wrel.mm"
include "wb.mm"
include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wss.mm"
include "cco.mm"
include "ccid.mm"
include "eqid.mm"
include "sectss.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "relbrcnvg.mm"
include "syl.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem isinv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume invfval.s: |- S = ( Sect ` C )


  assert |- ( ph -> ( F ( X N Y ) G <-> ( F ( X S Y ) G /\ G ( Y S X ) F ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    #
    wbr
    #
    cF
    cG
    cX
    cY
    cS
    co
    #
    wbr
    #
    cF
    cG
    cY
    cX
    cS
    co
    #
    ccnv
    #
    wbr
    #
    wa
    #
    @3
    cG
    cF
    @4
    wbr
    #
    wa
    wph
    @1
    cF
    cG
    @2
    @5
    cin
    #
    wbr
    @7
    wph
    @0
    @9
    cF
    cG
    wph
    cB
    cC
    cS
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invfval.s
    invfval
    breqd
    cF
    cG
    @2
    @5
    brin
    syl6bb
    wph
    @6
    @8
    @3
    wph
    @4
    wrel
    #
    @6
    @8
    wb
    wph
    @4
    cY
    cX
    cC
    chom
    cfv
    #
    co
    #
    cX
    cY
    @11
    co
    #
    cxp
    #
    wss
    @14
    wrel
    @10
    wph
    cB
    cC
    cS
    cC
    cco
    cfv
    #
    cC
    ccid
    cfv
    #
    @11
    cY
    cX
    invfval.b
    @11
    eqid
    @15
    eqid
    @16
    eqid
    invfval.s
    invfval.c
    invfval.y
    invfval.x
    sectss
    @12
    @13
    relxp
    @4
    @14
    relss
    mpisyl
    cF
    cG
    @4
    relbrcnvg
    syl
    anbi2d
    bitrd
end
