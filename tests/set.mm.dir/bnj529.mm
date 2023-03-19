include "wcel.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "word.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "biimpi.mm"
include "eleq2s.mm"
include "nnord.mm"
include "anim1i.mm"
include "ord0eln0.mm"
include "biimpar.mm"
include "3syl.mm"

theorem bnj529
  let cD: class D
  let cM: class M
  assume bnj529.1: |- D = ( _om \ { (/) } )


  assert |- ( M e. D -> (/) e. M )

  proof
    cM
    cD
    wcel
    cM
    com
    wcel
    #
    cM
    c0
    wne
    #
    wa
    #
    cM
    word
    #
    @1
    wa
    c0
    cM
    wcel
    #
    @2
    cM
    com
    c0
    csn
    cdif
    #
    cD
    cM
    @5
    wcel
    @2
    cM
    com
    c0
    eldifsn
    biimpi
    bnj529.1
    eleq2s
    @0
    @3
    @1
    cM
    nnord
    anim1i
    @3
    @4
    @1
    cM
    ord0eln0
    biimpar
    3syl
end
