include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wceq.mm"
include "ccrcts.mm"
include "wbr.mm"
include "cwlks.mm"
include "crctiswlk.mm"
include "wlkf.mm"
include "3syl.mm"
include "cc0.mm"
include "cfzo.mm"
include "elfzoelz.mm"
include "syl.mm"
include "cshwlen.mm"
include "syl2anc.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem crctcshlem2
  let wph: wff ph
  let cP: class P
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )


  assert |- ( ph -> ( # ` H ) = N )

  proof
    wph
    cF
    cS
    ccsh
    co
    #
    chash
    cfv
    #
    cF
    chash
    cfv
    #
    cH
    chash
    cfv
    cN
    wph
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cS
    cz
    wcel
    #
    @1
    @2
    wceq
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @4
    crctcsh.d
    cP
    cF
    cG
    crctiswlk
    cP
    cF
    cG
    cI
    crctcsh.i
    wlkf
    3syl
    wph
    cS
    cc0
    cN
    cfzo
    co
    wcel
    @5
    crctcsh.s
    cS
    cc0
    cN
    elfzoelz
    syl
    cS
    @3
    cF
    cshwlen
    syl2anc
    cH
    @0
    chash
    crctcsh.h
    fveq2i
    crctcsh.n
    3eqtr4g
end
