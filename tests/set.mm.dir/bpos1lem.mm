include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cz.mm"
include "wb.mm"
include "cprime.mm"
include "cn.mm"
include "prmnn.mm"
include "ax-mp.mm"
include "nnzi.mm"
include "eluzelz.mm"
include "eluz.mm"
include "sylancr.mm"
include "syl6bir.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wrex.mm"
include "cr.mm"
include "nnrei.mm"
include "a1i.mm"
include "nn0rei.mm"
include "2re.mm"
include "remulcli.mm"
include "eqeltrri.mm"
include "eluzelre.mm"
include "remulcl.mm"
include "wceq.mm"
include "wo.mm"
include "leloei.mm"
include "mpbir.mm"
include "nn0cni.mm"
include "2cn.mm"
include "mulcomli.mm"
include "eluzle.mm"
include "cc0.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an13.mm"
include "syl.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "letrd.mm"
include "anim2i.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "expcom.mm"
include "lelttric.mm"
include "mpjaod.mm"

theorem bpos1lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N
  let vp: setvar p
  assume bpos1.1: |- ( E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) -> ph )
  assume bpos1.2: |- ( N e. ( ZZ>= ` P ) -> ph )
  assume bpos1.3: |- P e. Prime
  assume bpos1.4: |- A e. NN0
  assume bpos1.5: |- ( A x. 2 ) = B
  assume bpos1.6: |- A < P
  assume bpos1.7: |- ( P < B \/ P = B )

  disjoint N p
  disjoint P p
  assert |- ( N e. ( ZZ>= ` A ) -> ph )

  proof
    cN
    cA
    cuz
    cfv
    wcel
    #
    cP
    cN
    cle
    wbr
    #
    wph
    cN
    cP
    clt
    wbr
    #
    @0
    @1
    cN
    cP
    cuz
    cfv
    wcel
    #
    wph
    @0
    cP
    cz
    wcel
    cN
    cz
    wcel
    @3
    @1
    wb
    cP
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    bpos1.3
    cP
    prmnn
    ax-mp
    #
    nnzi
    cA
    cN
    eluzelz
    cP
    cN
    eluz
    sylancr
    bpos1.2
    syl6bir
    @2
    @0
    wph
    @2
    @0
    wa
    #
    cN
    vp
    cv
    #
    clt
    wbr
    #
    @7
    c2
    cN
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    vp
    cprime
    wrex
    #
    wph
    @6
    @4
    @2
    cP
    @9
    cle
    wbr
    #
    wa
    #
    @12
    bpos1.3
    @0
    @13
    @2
    @0
    cP
    cB
    @9
    cP
    cr
    wcel
    #
    @0
    cP
    @5
    nnrei
    #
    a1i
    cB
    cr
    wcel
    @0
    cA
    c2
    cmul
    co
    cB
    cr
    bpos1.5
    cA
    c2
    cA
    bpos1.4
    nn0rei
    #
    2re
    remulcli
    eqeltrri
    #
    a1i
    @0
    c2
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @9
    cr
    wcel
    2re
    cA
    cN
    eluzelre
    #
    c2
    cN
    remulcl
    sylancr
    cP
    cB
    cle
    wbr
    #
    @0
    @22
    cP
    cB
    clt
    wbr
    cP
    cB
    wceq
    wo
    bpos1.7
    cP
    cB
    @16
    @18
    leloei
    mpbir
    a1i
    @0
    cB
    c2
    cA
    cmul
    co
    #
    @9
    cle
    cA
    c2
    cB
    cA
    bpos1.4
    nn0cni
    2cn
    bpos1.5
    mulcomli
    @0
    cA
    cN
    cle
    wbr
    #
    @23
    @9
    cle
    wbr
    #
    cA
    cN
    eluzle
    @0
    @20
    @24
    @25
    wb
    #
    @21
    cA
    cr
    wcel
    @20
    @19
    cc0
    c2
    clt
    wbr
    #
    wa
    @26
    @17
    @19
    @27
    2re
    2pos
    pm3.2i
    cA
    cN
    c2
    lemul2
    mp3an13
    syl
    mpbid
    syl5eqbrr
    letrd
    anim2i
    @11
    @14
    vp
    cP
    cprime
    @7
    cP
    wceq
    @8
    @2
    @10
    @13
    @7
    cP
    cN
    clt
    breq2
    @7
    cP
    @9
    cle
    breq1
    anbi12d
    rspcev
    sylancr
    bpos1.1
    syl
    expcom
    @0
    @15
    @20
    @1
    @2
    wo
    @16
    @21
    cP
    cN
    lelttric
    sylancr
    mpjaod
end
