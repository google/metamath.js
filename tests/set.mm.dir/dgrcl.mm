include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cdgr.mm"
include "ccoe.mm"
include "ccnv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cn0.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "dgrval.mm"
include "wor.mm"
include "cr.mm"
include "wss.mm"
include "nn0ssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "cz.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "0zd.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cun.mm"
include "wf.mm"
include "wceq.mm"
include "coef.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "dgrlem.mm"
include "simprd.mm"
include "nn0uz.mm"
include "uzsupss.mm"
include "syl3anc.mm"
include "supcl.mm"
include "eqeltrd.mm"

theorem dgrcl
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  let cM: class M
  let cN: class N
  let cX: class X


  assert |- ( F e. ( Poly ` S ) -> ( deg ` F ) e. NN0 )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    cdgr
    cfv
    cF
    ccoe
    cfv
    #
    ccnv
    cc
    cc0
    csn
    #
    cdif
    #
    cima
    #
    cn0
    clt
    csup
    cn0
    @1
    cS
    cF
    @1
    eqid
    #
    dgrval
    @0
    vn
    vx
    vy
    cn0
    @4
    clt
    cn0
    clt
    wor
    #
    @0
    cn0
    cr
    wss
    cr
    clt
    wor
    @6
    nn0ssre
    ltso
    cn0
    cr
    clt
    soss
    mp2
    a1i
    @0
    cc0
    cz
    wcel
    @4
    cn0
    wss
    vx
    cv
    #
    vn
    cv
    #
    cle
    wbr
    vx
    @4
    wral
    vn
    cz
    wrex
    #
    @8
    @7
    clt
    wbr
    wn
    vx
    @4
    wral
    @7
    @8
    clt
    wbr
    @7
    vy
    cv
    clt
    wbr
    vy
    @4
    wrex
    wi
    vx
    cn0
    wral
    wa
    vn
    cn0
    wrex
    @0
    0zd
    @0
    @1
    cdm
    #
    @4
    cn0
    @1
    @3
    cnvimass
    @0
    cn0
    cS
    @2
    cun
    #
    @1
    wf
    #
    @10
    cn0
    wceq
    @1
    cS
    cF
    @5
    coef
    cn0
    @11
    @1
    fdm
    syl
    syl5sseq
    @0
    @12
    @9
    vx
    @1
    cS
    vn
    cF
    @5
    dgrlem
    simprd
    vn
    vx
    vy
    @4
    cc0
    cn0
    nn0uz
    uzsupss
    syl3anc
    supcl
    eqeltrd
end
