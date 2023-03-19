include "cv.mm"
include "cdg1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cco1.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "wss.mm"
include "wi.mm"
include "ssrexv.mm"
include "syl.mm"
include "ss2abdv.mm"
include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "eqid.mm"
include "hbtlem1.mm"
include "syl3anc.mm"
include "3sstr4d.mm"

theorem hbtlem3
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem3.r: |- ( ph -> R e. Ring )
  assume hbtlem3.i: |- ( ph -> I e. U )
  assume hbtlem3.j: |- ( ph -> J e. U )
  assume hbtlem3.ij: |- ( ph -> I C_ J )
  assume hbtlem3.x: |- ( ph -> X e. NN0 )


  assert |- ( ph -> ( ( S ` I ) ` X ) C_ ( ( S ` J ) ` X ) )

  proof
    wph
    vb
    cv
    #
    cR
    cdg1
    cfv
    #
    cfv
    cX
    cle
    wbr
    va
    cv
    cX
    @0
    cco1
    cfv
    cfv
    wceq
    wa
    #
    vb
    cI
    wrex
    #
    va
    cab
    #
    @2
    vb
    cJ
    wrex
    #
    va
    cab
    #
    cX
    cI
    cS
    cfv
    cfv
    #
    cX
    cJ
    cS
    cfv
    cfv
    #
    wph
    @3
    @5
    va
    wph
    cI
    cJ
    wss
    @3
    @5
    wi
    hbtlem3.ij
    @2
    vb
    cI
    cJ
    ssrexv
    syl
    ss2abdv
    wph
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    cX
    cn0
    wcel
    #
    @7
    @4
    wceq
    hbtlem3.r
    hbtlem3.i
    hbtlem3.x
    @1
    cP
    cR
    cS
    cU
    va
    vb
    cI
    crg
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @1
    eqid
    #
    hbtlem1
    syl3anc
    wph
    @9
    cJ
    cU
    wcel
    @10
    @8
    @6
    wceq
    hbtlem3.r
    hbtlem3.j
    hbtlem3.x
    @1
    cP
    cR
    cS
    cU
    va
    vb
    cJ
    crg
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @11
    hbtlem1
    syl3anc
    3sstr4d
end
