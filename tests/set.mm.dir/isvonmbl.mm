include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "cmap.mm"
include "wss.mm"
include "dmvon.mm"
include "eleq2d.mm"
include "ovnome.mm"
include "eqid.mm"
include "caragenel.mm"
include "elpwi.mm"
include "adantl.mm"
include "unidmovn.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "ex.mm"
include "simpr.mm"
include "eqcomd.mm"
include "wb.mm"
include "cvv.mm"
include "ovex.mm"
include "ssex.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "impbid.mm"
include "pweqd.mm"
include "raleq.mm"
include "anbi12d.mm"
include "3bitrd.mm"

theorem isvonmbl
  let wph: wff ph
  let cE: class E
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume isvonmbl.1: |- ( ph -> X e. Fin )

  disjoint E a
  disjoint X a
  disjoint k x
  assert |- ( ph -> ( E e. dom ( voln ` X ) <-> ( E C_ ( RR ^m X ) /\ A. a e. ~P ( RR ^m X ) ( ( ( voln* ` X ) ` ( a i^i E ) ) +e ( ( voln* ` X ) ` ( a \ E ) ) ) = ( ( voln* ` X ) ` a ) ) ) )

  proof
    wph
    cE
    cX
    cvoln
    cfv
    cdm
    #
    wcel
    cE
    cX
    covoln
    cfv
    #
    ccaragen
    cfv
    #
    wcel
    cE
    @1
    cdm
    cuni
    #
    cpw
    #
    wcel
    #
    va
    cv
    #
    cE
    cin
    @1
    cfv
    @6
    cE
    cdif
    @1
    cfv
    cxad
    co
    @6
    @1
    cfv
    wceq
    #
    va
    @4
    wral
    #
    wa
    cE
    cr
    cX
    cmap
    co
    #
    wss
    #
    @7
    va
    @9
    cpw
    #
    wral
    #
    wa
    wph
    @0
    @2
    cE
    wph
    cX
    isvonmbl.1
    dmvon
    eleq2d
    wph
    @2
    cE
    @1
    va
    wph
    cX
    isvonmbl.1
    ovnome
    @2
    eqid
    caragenel
    wph
    @5
    @10
    @8
    @12
    wph
    @5
    @10
    wph
    @5
    @10
    wph
    @5
    wa
    cE
    @3
    @9
    @5
    cE
    @3
    wss
    #
    wph
    cE
    @3
    elpwi
    adantl
    wph
    @3
    @9
    wceq
    @5
    wph
    cX
    isvonmbl.1
    unidmovn
    #
    adantr
    sseqtrd
    ex
    wph
    @10
    @5
    wph
    @10
    wa
    #
    @5
    @13
    @15
    cE
    @9
    @3
    wph
    @10
    simpr
    wph
    @9
    @3
    wceq
    @10
    wph
    @3
    @9
    @14
    eqcomd
    adantr
    sseqtrd
    @10
    @5
    @13
    wb
    #
    wph
    @10
    cE
    cvv
    wcel
    @16
    cE
    @9
    cr
    cX
    cmap
    ovex
    ssex
    cE
    @3
    cvv
    elpwg
    syl
    adantl
    mpbird
    ex
    impbid
    wph
    @4
    @11
    wceq
    @8
    @12
    wb
    wph
    @3
    @9
    @14
    pweqd
    @7
    va
    @4
    @11
    raleq
    syl
    anbi12d
    3bitrd
end
