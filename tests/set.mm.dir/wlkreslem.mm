include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "df-br.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "wa.mm"
include "cvtx.mm"
include "wceq.mm"
include "syl6eq.mm"
include "anim1i.mm"
include "ancomd.mm"
include "wlk0prc.mm"
include "eqneqall.mm"
include "3syl.mm"
include "expcom.mm"
include "com13.mm"
include "syl.mm"
include "sylbi.mm"
include "mpcom.mm"
include "com12.mm"
include "sylbir.mm"
include "pm2.61i.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "wfun.mm"
include "cdm.mm"
include "cword.mm"
include "wlkf.mm"
include "chash.mm"
include "wrdf.mm"
include "ffund.mm"
include "ovex.mm"
include "resfunexg.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "cfz.mm"
include "wf.mm"
include "wlkp.mm"
include "ffun.mm"
include "3jca.mm"

theorem wlkreslem
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
  assume wlkres.v: |- V = ( Vtx ` G )
  assume wlkres.i: |- I = ( iEdg ` G )
  assume wlkres.d: |- ( ph -> F ( Walks ` G ) P )
  assume wlkres.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume wlkres.s: |- ( ph -> ( Vtx ` S ) = V )
  assume wlkres.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume wlkres.h: |- H = ( F |` ( 0 ..^ N ) )
  assume wlkres.q: |- Q = ( P |` ( 0 ... N ) )


  assert |- ( ph -> ( S e. _V /\ H e. _V /\ Q e. _V ) )

  proof
    wph
    cS
    cvv
    wcel
    #
    cH
    cvv
    wcel
    cQ
    cvv
    wcel
    @0
    wph
    @0
    wi
    #
    @0
    wph
    ax-1
    @0
    wn
    cS
    cvv
    wnel
    #
    @1
    cS
    cvv
    df-nel
    wph
    @2
    @0
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    #
    wph
    @2
    @0
    wi
    #
    wlkres.d
    @4
    cF
    cP
    cop
    #
    @3
    wcel
    #
    wph
    @5
    wi
    #
    cF
    cP
    @3
    df-br
    @7
    @3
    c0
    wne
    #
    @8
    @3
    @6
    ne0i
    @2
    wph
    @9
    @0
    wph
    @2
    @9
    @0
    wi
    #
    wph
    @2
    wa
    #
    @2
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wceq
    #
    wa
    @3
    c0
    wceq
    @10
    @11
    @14
    @2
    wph
    @14
    @2
    wph
    @12
    cV
    @13
    wlkres.s
    wlkres.v
    syl6eq
    anim1i
    ancomd
    cS
    cG
    wlk0prc
    @0
    @3
    c0
    eqneqall
    3syl
    expcom
    com13
    syl
    sylbi
    mpcom
    com12
    sylbir
    pm2.61i
    wph
    cH
    cF
    cc0
    cN
    cfzo
    co
    #
    cres
    #
    cvv
    wlkres.h
    wph
    cF
    wfun
    #
    @15
    cvv
    wcel
    @16
    cvv
    wcel
    wph
    @4
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @17
    wlkres.d
    cP
    cF
    cG
    cI
    wlkres.i
    wlkf
    @19
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    @18
    cF
    @18
    cF
    wrdf
    ffund
    3syl
    cc0
    cN
    cfzo
    ovex
    cF
    @15
    cvv
    resfunexg
    sylancl
    syl5eqel
    wph
    cQ
    cP
    cc0
    cN
    cfz
    co
    #
    cres
    #
    cvv
    wlkres.q
    wph
    cP
    wfun
    #
    @21
    cvv
    wcel
    @22
    cvv
    wcel
    wph
    @4
    cc0
    @20
    cfz
    co
    #
    cV
    cP
    wf
    @23
    wlkres.d
    cP
    cF
    cG
    cV
    wlkres.v
    wlkp
    @24
    cV
    cP
    ffun
    3syl
    cc0
    cN
    cfz
    ovex
    cP
    @21
    cvv
    resfunexg
    sylancl
    syl5eqel
    3jca
end
