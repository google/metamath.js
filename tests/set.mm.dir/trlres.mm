include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "trliswlk.mm"
include "syl.mm"
include "wlkres.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "wf1o.mm"
include "wf1.mm"
include "trlreslem.mm"
include "f1of1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "3syl.mm"
include "istrl.mm"
include "sylanbrc.mm"

theorem trlres
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume trlres.v: |- V = ( Vtx ` G )
  assume trlres.i: |- I = ( iEdg ` G )
  assume trlres.d: |- ( ph -> F ( Trails ` G ) P )
  assume trlres.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume trlres.h: |- H = ( F |` ( 0 ..^ N ) )
  assume trlres.s: |- ( ph -> ( Vtx ` S ) = V )
  assume trlres.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume trlres.q: |- Q = ( P |` ( 0 ... N ) )


  assert |- ( ph -> H ( Trails ` S ) Q )

  proof
    wph
    cH
    cQ
    cS
    cwlks
    cfv
    wbr
    cH
    ccnv
    wfun
    #
    cH
    cQ
    cS
    ctrls
    cfv
    wbr
    wph
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    trlres.v
    trlres.i
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    trlres.d
    cP
    cF
    cG
    trliswlk
    syl
    trlres.n
    trlres.s
    trlres.e
    trlres.h
    trlres.q
    wlkres
    wph
    cc0
    cH
    chash
    cfv
    cfzo
    co
    #
    cI
    cF
    cc0
    cN
    cfzo
    co
    cima
    cres
    cdm
    #
    cH
    wf1o
    @1
    @2
    cH
    wf1
    #
    @0
    wph
    cP
    cF
    cG
    cH
    cI
    cN
    cV
    trlres.v
    trlres.i
    trlres.d
    trlres.n
    trlres.h
    trlreslem
    @1
    @2
    cH
    f1of1
    @3
    @1
    @2
    cH
    wf
    @0
    @1
    @2
    cH
    df-f1
    simprbi
    3syl
    cQ
    cH
    cS
    istrl
    sylanbrc
end
