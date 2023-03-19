include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wrex.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "wcel.mm"
include "w3a.mm"
include "nf3an.mm"
include "1zzd.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "3ad2antl1.mm"
include "cc0.mm"
include "cle.mm"
include "crp.mm"
include "simp2.mm"
include "simp3.mm"
include "fmul01lt1lem2.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem fmul01lt1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cM: class M
  assume fmul01lt1.1: |- F/_ i B
  assume fmul01lt1.2: |- F/ i ph
  assume fmul01lt1.3: |- F/_ j A
  assume fmul01lt1.4: |- A = seq 1 ( x. , B )
  assume fmul01lt1.5: |- ( ph -> M e. NN )
  assume fmul01lt1.6: |- ( ph -> B : ( 1 ... M ) --> RR )
  assume fmul01lt1.7: |- ( ( ph /\ i e. ( 1 ... M ) ) -> 0 <_ ( B ` i ) )
  assume fmul01lt1.8: |- ( ( ph /\ i e. ( 1 ... M ) ) -> ( B ` i ) <_ 1 )
  assume fmul01lt1.9: |- ( ph -> E e. RR+ )
  assume fmul01lt1.10: |- ( ph -> E. j e. ( 1 ... M ) ( B ` j ) < E )

  disjoint i j
  disjoint E i
  disjoint E j
  disjoint M i
  disjoint M j
  disjoint j ph
  assert |- ( ph -> ( A ` M ) < E )

  proof
    wph
    vj
    cv
    #
    cB
    cfv
    #
    cE
    clt
    wbr
    #
    vj
    c1
    cM
    cfz
    co
    #
    wrex
    cM
    cA
    cfv
    #
    cE
    clt
    wbr
    #
    fmul01lt1.10
    wph
    @2
    @5
    vj
    @3
    wph
    vj
    nfv
    vj
    @4
    cE
    clt
    vj
    cM
    cA
    fmul01lt1.3
    vj
    cM
    nfcv
    nffv
    vj
    clt
    nfcv
    vj
    cE
    nfcv
    nfbr
    wph
    @0
    @3
    wcel
    #
    @2
    @5
    wph
    @6
    @2
    w3a
    #
    cA
    cB
    vi
    cE
    @0
    c1
    cM
    fmul01lt1.1
    wph
    @6
    @2
    vi
    fmul01lt1.2
    @6
    vi
    nfv
    vi
    @1
    cE
    clt
    vi
    @0
    cB
    fmul01lt1.1
    vi
    @0
    nfcv
    nffv
    vi
    clt
    nfcv
    vi
    cE
    nfcv
    nfbr
    nf3an
    fmul01lt1.4
    @7
    1zzd
    wph
    @6
    cM
    c1
    cuz
    cfv
    wcel
    #
    @2
    wph
    cM
    cn
    wcel
    @8
    fmul01lt1.5
    cM
    elnnuz
    sylib
    3ad2ant1
    wph
    @6
    vi
    cv
    #
    @3
    wcel
    #
    @9
    cB
    cfv
    #
    cr
    wcel
    @2
    wph
    @3
    cr
    @9
    cB
    fmul01lt1.6
    ffvelrnda
    3ad2antl1
    wph
    @6
    @10
    cc0
    @11
    cle
    wbr
    @2
    fmul01lt1.7
    3ad2antl1
    wph
    @6
    @10
    @11
    c1
    cle
    wbr
    @2
    fmul01lt1.8
    3ad2antl1
    wph
    @6
    cE
    crp
    wcel
    @2
    fmul01lt1.9
    3ad2ant1
    wph
    @6
    @2
    simp2
    wph
    @6
    @2
    simp3
    fmul01lt1lem2
    3exp
    rexlimd
    mpd
end
