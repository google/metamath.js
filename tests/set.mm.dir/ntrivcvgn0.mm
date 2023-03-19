include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "cvv.mm"
include "climrel.mm"
include "brrelex2i.mm"
include "jca.mm"
include "wceq.mm"
include "neeq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem ntrivcvgn0
  let wph: wff ph
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume ntrivcvgn0.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvgn0.2: |- ( ph -> M e. ZZ )
  assume ntrivcvgn0.3: |- ( ph -> seq M ( x. , F ) ~~> X )
  assume ntrivcvgn0.4: |- ( ph -> X =/= 0 )

  disjoint F n
  disjoint F y
  disjoint M n
  disjoint M y
  disjoint n y
  disjoint X y
  disjoint Z n
  assert |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )

  proof
    wph
    cM
    cZ
    wcel
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    cF
    cM
    cseq
    #
    @0
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    @1
    cmul
    cF
    vn
    cv
    #
    cseq
    #
    @0
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    cZ
    wrex
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @11
    wcel
    ntrivcvgn0.2
    cM
    uzid
    syl
    ntrivcvgn0.1
    syl6eleqr
    wph
    cX
    cvv
    wcel
    #
    cX
    cc0
    wne
    #
    @2
    cX
    cli
    wbr
    #
    wa
    #
    @5
    wph
    @14
    @12
    ntrivcvgn0.3
    @2
    cX
    cli
    climrel
    brrelex2i
    syl
    wph
    @13
    @14
    ntrivcvgn0.4
    ntrivcvgn0.3
    jca
    @4
    @15
    vy
    cX
    cvv
    @0
    cX
    wceq
    @1
    @13
    @3
    @14
    @0
    cX
    cc0
    neeq1
    @0
    cX
    @2
    cli
    breq2
    anbi12d
    spcegv
    sylc
    @10
    @5
    vn
    cM
    cZ
    @6
    cM
    wceq
    #
    @9
    @4
    vy
    @16
    @8
    @3
    @1
    @16
    @7
    @2
    @0
    cli
    cmul
    cF
    @6
    cM
    seqeq1
    breq1d
    anbi2d
    exbidv
    rspcev
    syl2anc
end
