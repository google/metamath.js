include "cvv.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "cixp.mm"
include "cr.mm"
include "cmap.mm"
include "elexd.mm"
include "elmapfn.mm"
include "syl.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "wf.mm"
include "elmapi.mm"
include "c2.mm"
include "chash.mm"
include "csqrt.mm"
include "cmul.mm"
include "cdiv.mm"
include "cmin.mm"
include "cxr.mm"
include "cioo.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnred.mm"
include "nngt0d.mm"
include "elrpd.mm"
include "rpsqrtcld.mm"
include "rpmulcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "adantr.mm"
include "resubcld.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "ltled.mm"
include "caddc.mm"
include "readdcld.mm"
include "ioogtlb.mm"
include "elicod.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "elixp2.mm"
include "sylibr.mm"

theorem hoiqssbllem1
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cE: class E
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume hoiqssbllem1.i: |- F/ i ph
  assume hoiqssbllem1.x: |- ( ph -> X e. Fin )
  assume hoiqssbllem1.n: |- ( ph -> X =/= (/) )
  assume hoiqssbllem1.y: |- ( ph -> Y e. ( RR ^m X ) )
  assume hoiqssbllem1.c: |- ( ph -> C : X --> RR )
  assume hoiqssbllem1.d: |- ( ph -> D : X --> RR )
  assume hoiqssbllem1.e: |- ( ph -> E e. RR+ )
  assume hoiqssbllem1.l: |- ( ( ph /\ i e. X ) -> ( C ` i ) e. ( ( ( Y ` i ) - ( E / ( 2 x. ( sqrt ` ( # ` X ) ) ) ) ) (,) ( Y ` i ) ) )
  assume hoiqssbllem1.r: |- ( ( ph /\ i e. X ) -> ( D ` i ) e. ( ( Y ` i ) (,) ( ( Y ` i ) + ( E / ( 2 x. ( sqrt ` ( # ` X ) ) ) ) ) ) )

  disjoint X i
  disjoint Y i
  disjoint k x
  assert |- ( ph -> Y e. X_ i e. X ( ( C ` i ) [,) ( D ` i ) ) )

  proof
    wph
    cY
    cvv
    wcel
    #
    cY
    cX
    wfn
    #
    vi
    cv
    #
    cY
    cfv
    #
    @2
    cC
    cfv
    #
    @2
    cD
    cfv
    #
    cico
    co
    #
    wcel
    #
    vi
    cX
    wral
    #
    w3a
    cY
    vi
    cX
    @6
    cixp
    wcel
    wph
    @0
    @1
    @8
    wph
    cY
    cr
    cX
    cmap
    co
    #
    hoiqssbllem1.y
    elexd
    wph
    cY
    @9
    wcel
    #
    @1
    hoiqssbllem1.y
    cY
    cr
    cX
    elmapfn
    syl
    wph
    @7
    vi
    cX
    hoiqssbllem1.i
    wph
    @2
    cX
    wcel
    #
    @7
    wph
    @11
    wa
    #
    @4
    @5
    @3
    @12
    @4
    wph
    cX
    cr
    @2
    cC
    hoiqssbllem1.c
    ffvelrnda
    #
    rexrd
    @12
    @5
    wph
    cX
    cr
    @2
    cD
    hoiqssbllem1.d
    ffvelrnda
    rexrd
    @12
    @3
    wph
    cX
    cr
    @2
    cY
    wph
    @10
    cX
    cr
    cY
    wf
    hoiqssbllem1.y
    cY
    cr
    cX
    elmapi
    syl
    ffvelrnda
    #
    rexrd
    #
    @12
    @4
    @3
    @13
    @14
    @12
    @3
    cE
    c2
    cX
    chash
    cfv
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    cxr
    wcel
    @3
    cxr
    wcel
    #
    @4
    @20
    @3
    cioo
    co
    wcel
    @4
    @3
    clt
    wbr
    @12
    @20
    @12
    @3
    @19
    @14
    wph
    @19
    cr
    wcel
    @11
    wph
    @19
    wph
    cE
    @18
    hoiqssbllem1.e
    wph
    c2
    @17
    c2
    crp
    wcel
    wph
    2rp
    a1i
    wph
    @16
    wph
    @16
    wph
    @16
    wph
    @16
    cn
    wcel
    #
    cX
    c0
    wne
    #
    hoiqssbllem1.n
    wph
    cX
    cfn
    wcel
    @22
    @23
    wb
    hoiqssbllem1.x
    cX
    hashnncl
    syl
    mpbird
    #
    nnred
    wph
    @16
    @24
    nngt0d
    elrpd
    rpsqrtcld
    rpmulcld
    rpdivcld
    rpred
    adantr
    #
    resubcld
    rexrd
    @15
    hoiqssbllem1.l
    @20
    @3
    @4
    iooltub
    syl3anc
    ltled
    @12
    @21
    @3
    @19
    caddc
    co
    #
    cxr
    wcel
    @5
    @3
    @26
    cioo
    co
    wcel
    @3
    @5
    clt
    wbr
    @15
    @12
    @26
    @12
    @3
    @19
    @14
    @25
    readdcld
    rexrd
    hoiqssbllem1.r
    @3
    @26
    @5
    ioogtlb
    syl3anc
    elicod
    ex
    ralrimi
    3jca
    vi
    cX
    @6
    cY
    elixp2
    sylibr
end
