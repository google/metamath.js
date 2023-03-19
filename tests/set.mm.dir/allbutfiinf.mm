include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "a1i.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "sseqtri.mm"
include "wrex.mm"
include "allbutfi.mm"
include "sylib.mm"
include "wi.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfne.mm"
include "wa.mm"
include "rabid.mm"
include "bicomi.mm"
include "biimpi.mm"
include "ne0i.mm"
include "syl.mm"
include "ex.mm"
include "rexlimi.mm"
include "mpd.mm"
include "infssuzcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "nfinf.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfv.mm"
include "nfral.mm"
include "nfra1.mm"
include "nfrab.mm"
include "fveq2.mm"
include "raleqd.mm"
include "elrabf.mm"
include "simprd.mm"
include "jca.mm"

theorem allbutfiinf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume allbutfiinf.z: |- Z = ( ZZ>= ` M )
  assume allbutfiinf.a: |- A = U_ n e. Z |^|_ m e. ( ZZ>= ` n ) B
  assume allbutfiinf.x: |- ( ph -> X e. A )
  assume allbutfiinf.n: |- N = inf ( { n e. Z | A. m e. ( ZZ>= ` n ) X e. B } , RR , < )

  disjoint B n
  disjoint X m
  disjoint X n
  disjoint m n
  disjoint Z m
  disjoint Z n
  assert |- ( ph -> ( N e. Z /\ A. m e. ( ZZ>= ` N ) X e. B ) )

  proof
    wph
    cN
    cZ
    wcel
    #
    cX
    cB
    wcel
    #
    vm
    cN
    cuz
    cfv
    #
    wral
    #
    wph
    @1
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
    crab
    #
    cZ
    cN
    @6
    vn
    cZ
    ssrab2
    #
    wph
    cN
    @7
    cr
    clt
    cinf
    #
    @7
    cN
    @9
    wceq
    wph
    allbutfiinf.n
    a1i
    wph
    @7
    cM
    cuz
    cfv
    #
    wss
    #
    @7
    c0
    wne
    #
    @9
    @7
    wcel
    @11
    wph
    @7
    cZ
    @10
    @8
    allbutfiinf.z
    sseqtri
    a1i
    wph
    @6
    vn
    cZ
    wrex
    #
    @12
    wph
    cX
    cA
    wcel
    @13
    allbutfiinf.x
    cA
    cB
    vm
    vn
    cM
    cX
    cZ
    allbutfiinf.z
    allbutfiinf.a
    allbutfi
    sylib
    @13
    @12
    wi
    wph
    @6
    @12
    vn
    cZ
    vn
    @7
    c0
    @6
    vn
    cZ
    nfrab1
    #
    vn
    c0
    nfcv
    nfne
    @4
    cZ
    wcel
    #
    @6
    @12
    @15
    @6
    wa
    #
    @4
    @7
    wcel
    #
    @12
    @16
    @17
    @17
    @16
    @6
    vn
    cZ
    rabid
    bicomi
    biimpi
    @7
    @4
    ne0i
    syl
    ex
    rexlimi
    a1i
    mpd
    @7
    cM
    infssuzcl
    syl2anc
    eqeltrd
    #
    sseldi
    wph
    cN
    @7
    wcel
    #
    @3
    @18
    @19
    @0
    @3
    @19
    @0
    @3
    wa
    @6
    @3
    vn
    cN
    cZ
    vn
    cN
    @9
    allbutfiinf.n
    vn
    @7
    cr
    clt
    @14
    vn
    cr
    nfcv
    vn
    clt
    nfcv
    nfinf
    nfcxfr
    #
    vn
    cZ
    nfcv
    @1
    vn
    vm
    @2
    vn
    cN
    cuz
    vn
    cuz
    nfcv
    @20
    nffv
    @1
    vn
    nfv
    nfral
    @4
    cN
    wceq
    @1
    vm
    @5
    @2
    vm
    @5
    nfcv
    vm
    cN
    cuz
    vm
    cuz
    nfcv
    vm
    cN
    @9
    allbutfiinf.n
    vm
    @7
    cr
    clt
    @6
    vm
    vn
    cZ
    @1
    vm
    @5
    nfra1
    vm
    cZ
    nfcv
    nfrab
    vm
    cr
    nfcv
    vm
    clt
    nfcv
    nfinf
    nfcxfr
    nffv
    @4
    cN
    cuz
    fveq2
    raleqd
    elrabf
    biimpi
    simprd
    syl
    jca
end
