include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvtx.mm"
include "cfv.mm"
include "cbs.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cnx.mm"
include "cedgf.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "fvexi.mm"
include "a1i.mm"
include "setsn0fun.mm"
include "eqcomi.mm"
include "preq2i.mm"
include "basprssdmsets.mm"
include "syl5eqss.mm"
include "funvtxval.mm"
include "syl2anc.mm"
include "baseid.mm"
include "slotsbaseefdif.mm"
include "neeqtrri.mm"
include "setsnid.mm"
include "syl6eqr.mm"

theorem setsvtx
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  assume setsvtx.i: |- I = ( .ef ` ndx )
  assume setsvtx.s: |- ( ph -> G Struct X )
  assume setsvtx.b: |- ( ph -> ( Base ` ndx ) e. dom G )
  assume setsvtx.e: |- ( ph -> E e. W )


  assert |- ( ph -> ( Vtx ` ( G sSet <. I , E >. ) ) = ( Base ` G ) )

  proof
    wph
    cG
    cI
    cE
    cop
    csts
    co
    #
    cvtx
    cfv
    #
    @0
    cbs
    cfv
    #
    cG
    cbs
    cfv
    wph
    @0
    c0
    csn
    cdif
    wfun
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cpr
    #
    @0
    cdm
    #
    wss
    @1
    @2
    wceq
    wph
    cG
    cvv
    cE
    cI
    cW
    cX
    setsvtx.s
    cI
    cvv
    wcel
    wph
    cI
    cnx
    cedgf
    setsvtx.i
    fvexi
    a1i
    #
    setsvtx.e
    setsn0fun
    wph
    @5
    @3
    cI
    cpr
    @6
    @4
    cI
    @3
    cI
    @4
    setsvtx.i
    eqcomi
    preq2i
    wph
    cG
    cvv
    cE
    cI
    cW
    cX
    setsvtx.s
    @7
    setsvtx.e
    setsvtx.b
    basprssdmsets
    syl5eqss
    @0
    funvtxval
    syl2anc
    cE
    cI
    cbs
    cG
    baseid
    @3
    @4
    cI
    slotsbaseefdif
    setsvtx.i
    neeqtrri
    setsnid
    syl6eqr
end
