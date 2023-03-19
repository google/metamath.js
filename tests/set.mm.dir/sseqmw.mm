include "cword.mm"
include "chash.mm"
include "ccnv.mm"
include "cfv.mm"
include "cuz.mm"
include "cima.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "uzid.mm"
include "3syl.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "wfn.mm"
include "wa.mm"
include "wb.mm"
include "hashf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "elind.mm"
include "syl6eleqr.mm"

theorem sseqmw
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )


  assert |- ( ph -> M e. W )

  proof
    wph
    cM
    cS
    cword
    #
    chash
    ccnv
    cM
    chash
    cfv
    #
    cuz
    cfv
    #
    cima
    #
    cin
    cW
    wph
    @0
    @3
    cM
    sseqval.2
    wph
    cM
    cvv
    wcel
    #
    @1
    @2
    wcel
    #
    cM
    @3
    wcel
    #
    wph
    cM
    @0
    wcel
    #
    @4
    sseqval.2
    cM
    @0
    elex
    syl
    wph
    @7
    @1
    cz
    wcel
    @5
    sseqval.2
    @7
    @1
    cS
    cM
    lencl
    nn0zd
    @1
    uzid
    3syl
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    chash
    cvv
    wfn
    @6
    @4
    @5
    wa
    wb
    hashf
    cvv
    @8
    chash
    ffn
    cvv
    cM
    @2
    chash
    elpreima
    mp2b
    sylanbrc
    elind
    sseqval.3
    syl6eleqr
end
