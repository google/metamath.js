include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "ciin.mm"
include "ciun.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "allbutfi.mm"
include "sylib.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wi.mm"
include "simpll.mm"
include "uztrn2.mm"
include "ssd.mm"
include "sselda.mm"
include "adantll.mm"
include "ffvelrnda.mm"
include "ex.mm"
include "syl2anc.mm"
include "ralimdaa.mm"
include "reximdva.mm"
include "mpd.mm"

theorem allbutfifvre
  let wph: wff ph
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  assume allbutfifvre.1: |- F/ m ph
  assume allbutfifvre.2: |- Z = ( ZZ>= ` M )
  assume allbutfifvre.3: |- ( ( ph /\ m e. Z ) -> ( F ` m ) : dom ( F ` m ) --> RR )
  assume allbutfifvre.4: |- D = U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m )
  assume allbutfifvre.5: |- ( ph -> X e. D )

  disjoint X m
  disjoint X n
  disjoint m n
  disjoint Z m
  disjoint n ph
  disjoint Z j
  disjoint j n
  assert |- ( ph -> E. n e. Z A. m e. ( ZZ>= ` n ) ( ( F ` m ) ` X ) e. RR )

  proof
    wph
    cX
    vm
    cv
    #
    cF
    cfv
    #
    cdm
    #
    wcel
    #
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cZ
    wrex
    #
    cX
    @1
    cfv
    cr
    wcel
    #
    vm
    @5
    wral
    #
    vn
    cZ
    wrex
    wph
    cX
    vn
    cZ
    vm
    @5
    @2
    ciin
    ciun
    #
    wcel
    @7
    wph
    cX
    cD
    @10
    allbutfifvre.5
    allbutfifvre.4
    syl6eleq
    @10
    @2
    vm
    vn
    cM
    cX
    cZ
    allbutfifvre.2
    @10
    eqid
    allbutfi
    sylib
    wph
    @6
    @9
    vn
    cZ
    wph
    @4
    cZ
    wcel
    #
    wa
    #
    @3
    @8
    vm
    @5
    wph
    @11
    vm
    allbutfifvre.1
    @11
    vm
    nfv
    nfan
    @12
    @0
    @5
    wcel
    #
    wa
    wph
    @0
    cZ
    wcel
    #
    @3
    @8
    wi
    wph
    @11
    @13
    simpll
    @11
    @13
    @14
    wph
    @11
    @5
    cZ
    @0
    @11
    vj
    @5
    cZ
    cM
    vj
    cv
    @4
    cZ
    allbutfifvre.2
    uztrn2
    ssd
    sselda
    adantll
    wph
    @14
    wa
    #
    @3
    @8
    @15
    @2
    cr
    cX
    @1
    allbutfifvre.3
    ffvelrnda
    ex
    syl2anc
    ralimdaa
    reximdva
    mpd
end
