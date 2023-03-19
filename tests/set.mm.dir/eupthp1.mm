include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cdm.mm"
include "wf1o.mm"
include "ceupth.mm"
include "eupthiswlk.mm"
include "syl.mm"
include "ciedg.mm"
include "wceq.mm"
include "a1i.mm"
include "cvtx.mm"
include "wlkp1.mm"
include "cin.mm"
include "c0.mm"
include "wa.mm"
include "eupthi.mm"
include "wb.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "f1oeq2.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "3syl.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "f1osng.mm"
include "sylancr.mm"
include "cedg.mm"
include "dmsnopg.mm"
include "f1oeq3d.mm"
include "mpbird.mm"
include "fzodisjsn.mm"
include "ineq2d.mm"
include "wn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "c1.mm"
include "caddc.mm"
include "wlkp1lem2.mm"
include "oveq2d.mm"
include "cuz.mm"
include "cn0.mm"
include "wlkcl.mm"
include "eleq1i.mm"
include "elnn0uz.mm"
include "sylbb1.mm"
include "fzosplitsn.mm"
include "dmun.mm"
include "f1oeq123d.mm"
include "iseupthf1o.mm"
include "sylanbrc.mm"

theorem eupthp1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume eupthp1.v: |- V = ( Vtx ` G )
  assume eupthp1.i: |- I = ( iEdg ` G )
  assume eupthp1.f: |- ( ph -> Fun I )
  assume eupthp1.a: |- ( ph -> I e. Fin )
  assume eupthp1.b: |- ( ph -> B e. _V )
  assume eupthp1.c: |- ( ph -> C e. V )
  assume eupthp1.d: |- ( ph -> -. B e. dom I )
  assume eupthp1.p: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eupthp1.n: |- N = ( # ` F )
  assume eupthp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume eupthp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume eupthp1.u: |- ( iEdg ` S ) = ( I u. { <. B , E >. } )
  assume eupthp1.h: |- H = ( F u. { <. N , B >. } )
  assume eupthp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume eupthp1.s: |- ( Vtx ` S ) = V
  assume eupthp1.l: |- ( ( ph /\ C = ( P ` N ) ) -> E = { C } )


  assert |- ( ph -> H ( EulerPaths ` S ) Q )

  proof
    wph
    cH
    cQ
    cS
    cwlks
    cfv
    wbr
    cc0
    cH
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cB
    cE
    cop
    csn
    #
    cun
    #
    cdm
    #
    cH
    wf1o
    #
    cH
    cQ
    cS
    ceupth
    cfv
    wbr
    wph
    cB
    cC
    cP
    cQ
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    eupthp1.v
    eupthp1.i
    eupthp1.f
    eupthp1.a
    eupthp1.b
    eupthp1.c
    eupthp1.d
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    eupthp1.p
    cP
    cF
    cG
    eupthiswlk
    #
    syl
    #
    eupthp1.n
    eupthp1.e
    eupthp1.x
    cS
    ciedg
    cfv
    #
    @3
    wceq
    wph
    eupthp1.u
    a1i
    #
    eupthp1.h
    eupthp1.q
    cS
    cvtx
    cfv
    cV
    wceq
    wph
    eupthp1.s
    a1i
    eupthp1.l
    wlkp1
    wph
    @5
    cc0
    cN
    cfzo
    co
    #
    cN
    csn
    #
    cun
    #
    cI
    cdm
    #
    @2
    cdm
    #
    cun
    #
    cF
    cN
    cB
    cop
    csn
    #
    cun
    #
    wf1o
    #
    wph
    @12
    @15
    cF
    wf1o
    #
    @13
    @16
    @18
    wf1o
    #
    @12
    @13
    cin
    c0
    wceq
    #
    @15
    @16
    cin
    #
    c0
    wceq
    @20
    wph
    @6
    @7
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @15
    cF
    wf1o
    #
    wa
    @21
    eupthp1.p
    cP
    cF
    cG
    cI
    eupthp1.i
    eupthi
    @27
    @21
    @7
    @27
    @21
    @26
    @12
    wceq
    @27
    @21
    wb
    @25
    cN
    cc0
    cfzo
    cN
    @25
    eupthp1.n
    eqcomi
    oveq2i
    @26
    @12
    @15
    cF
    f1oeq2
    ax-mp
    biimpi
    adantl
    3syl
    wph
    @22
    @13
    cB
    csn
    #
    @18
    wf1o
    #
    wph
    cN
    cvv
    wcel
    cB
    cvv
    wcel
    @29
    cN
    @25
    cvv
    eupthp1.n
    cF
    chash
    fvex
    eqeltri
    eupthp1.b
    cN
    cB
    cvv
    cvv
    f1osng
    sylancr
    wph
    @16
    @28
    @13
    @18
    wph
    cE
    cG
    cedg
    cfv
    #
    wcel
    @16
    @28
    wceq
    eupthp1.e
    cB
    cE
    @30
    dmsnopg
    syl
    #
    f1oeq3d
    mpbird
    @23
    wph
    cc0
    cN
    fzodisjsn
    a1i
    wph
    @24
    @15
    @28
    cin
    #
    c0
    wph
    @16
    @28
    @15
    @31
    ineq2d
    wph
    cB
    @15
    wcel
    wn
    @32
    c0
    wceq
    eupthp1.d
    @15
    cB
    disjsn
    sylibr
    eqtrd
    @12
    @15
    @13
    @16
    cF
    @18
    f1oun
    syl22anc
    wph
    @1
    @14
    @4
    @17
    cH
    @19
    cH
    @19
    wceq
    wph
    eupthp1.h
    a1i
    wph
    @1
    cc0
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @14
    wph
    @0
    @33
    cc0
    cfzo
    wph
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    eupthp1.v
    eupthp1.i
    eupthp1.f
    eupthp1.a
    eupthp1.b
    eupthp1.c
    eupthp1.d
    @9
    eupthp1.n
    eupthp1.e
    eupthp1.x
    @11
    eupthp1.h
    wlkp1lem2
    oveq2d
    wph
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @34
    @14
    wceq
    wph
    @6
    @7
    @35
    eupthp1.p
    @8
    @7
    @25
    cn0
    wcel
    #
    @35
    cP
    cF
    cG
    wlkcl
    cN
    cn0
    wcel
    @36
    @35
    cN
    @25
    cn0
    eupthp1.n
    eleq1i
    cN
    elnn0uz
    sylbb1
    syl
    3syl
    cc0
    cN
    fzosplitsn
    syl
    eqtrd
    @4
    @17
    wceq
    wph
    cI
    @2
    dmun
    a1i
    f1oeq123d
    mpbird
    cQ
    cH
    cS
    @3
    @10
    @3
    eupthp1.u
    eqcomi
    iseupthf1o
    sylanbrc
end
