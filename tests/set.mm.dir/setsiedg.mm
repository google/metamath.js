include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "ciedg.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cbs.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "setsn0fun.mm"
include "basprssdmsets.mm"
include "funiedgval.mm"
include "syl2anc.mm"
include "opeq1i.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "a1i.mm"
include "wcel.mm"
include "cstr.mm"
include "wbr.mm"
include "structex.mm"
include "syl.mm"
include "edgfid.mm"
include "setsid.mm"
include "3eqtr4d.mm"

theorem setsiedg
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


  assert |- ( ph -> ( iEdg ` ( G sSet <. I , E >. ) ) = E )

  proof
    wph
    cG
    cnx
    cedgf
    cfv
    #
    cE
    cop
    #
    csts
    co
    #
    ciedg
    cfv
    #
    @2
    cedgf
    cfv
    #
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    ciedg
    cfv
    #
    cE
    wph
    @2
    c0
    csn
    cdif
    wfun
    cnx
    cbs
    cfv
    @0
    cpr
    @2
    cdm
    wss
    @3
    @4
    wceq
    wph
    cG
    cvv
    cE
    @0
    cW
    cX
    setsvtx.s
    wph
    cnx
    cedgf
    fvexd
    #
    setsvtx.e
    setsn0fun
    wph
    cG
    cvv
    cE
    @0
    cW
    cX
    setsvtx.s
    @8
    setsvtx.e
    setsvtx.b
    basprssdmsets
    @2
    funiedgval
    syl2anc
    @7
    @3
    wceq
    wph
    @6
    @2
    ciedg
    @5
    @1
    cG
    csts
    cI
    @0
    cE
    setsvtx.i
    opeq1i
    oveq2i
    fveq2i
    a1i
    wph
    cG
    cvv
    wcel
    #
    cE
    cW
    wcel
    cE
    @4
    wceq
    wph
    cG
    cX
    cstr
    wbr
    @9
    setsvtx.s
    cG
    cX
    structex
    syl
    setsvtx.e
    cvv
    cE
    cedgf
    cW
    cG
    edgfid
    setsid
    syl2anc
    3eqtr4d
end
