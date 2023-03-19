include "cc0.mm"
include "cfv.mm"
include "clsw.mm"
include "cwlkson.mm"
include "co.mm"
include "wbr.mm"
include "cwlks.mm"
include "wceq.mm"
include "chash.mm"
include "eqidd.mm"
include "c1.mm"
include "cmin.mm"
include "wlklenvm1.mm"
include "fveq2d.mm"
include "cvtx.mm"
include "cword.mm"
include "wcel.mm"
include "eqid.mm"
include "wlkpwrd.mm"
include "lsw.mm"
include "syl.mm"
include "eqtr4d.mm"
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "caddc.mm"
include "cn.mm"
include "cn0.mm"
include "wlkcl.mm"
include "nn0p1nn.mm"
include "wlklenvp1.mm"
include "jca32.mm"
include "fstwrdne0.mm"
include "lswlgt0cl.mm"
include "jca.mm"
include "ciedg.mm"
include "cdm.mm"
include "wlkf.mm"
include "wrdv.mm"
include "iswlkon.mm"
include "mpbir3and.mm"

theorem wlkonwlk1l
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  assume wlkonwlk1l.w: |- ( ph -> F ( Walks ` G ) P )


  assert |- ( ph -> F ( ( P ` 0 ) ( WalksOn ` G ) ( lastS ` P ) ) P )

  proof
    wph
    cF
    cP
    cc0
    cP
    cfv
    #
    cP
    clsw
    cfv
    #
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @0
    @0
    wceq
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    @1
    wceq
    #
    wlkonwlk1l.w
    wph
    @0
    eqidd
    wph
    @3
    @7
    wlkonwlk1l.w
    @3
    @6
    cP
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cP
    cfv
    #
    @1
    @3
    @5
    @9
    cP
    cP
    cF
    cG
    wlklenvm1
    fveq2d
    @3
    cP
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @1
    @10
    wceq
    cP
    cF
    cG
    @11
    @11
    eqid
    #
    wlkpwrd
    #
    cP
    @12
    lsw
    syl
    eqtr4d
    syl
    wph
    @0
    @11
    wcel
    #
    @1
    @11
    wcel
    #
    wa
    #
    cF
    cvv
    cword
    #
    wcel
    #
    @13
    wa
    wa
    #
    @2
    @3
    @4
    @7
    w3a
    wb
    wph
    @3
    @21
    wlkonwlk1l.w
    @3
    @18
    @20
    @13
    @3
    @5
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @13
    @8
    @22
    wceq
    #
    wa
    wa
    #
    @18
    @3
    @23
    @13
    @24
    @3
    @5
    cn0
    wcel
    @23
    cP
    cF
    cG
    wlkcl
    @5
    nn0p1nn
    syl
    @15
    cP
    cF
    cG
    wlklenvp1
    jca32
    @25
    @16
    @17
    @22
    @11
    cP
    fstwrdne0
    @22
    @11
    cP
    lswlgt0cl
    jca
    syl
    @3
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    @20
    cP
    cF
    cG
    @26
    @26
    eqid
    wlkf
    @27
    cF
    wrdv
    syl
    @15
    jca32
    syl
    @0
    @1
    cP
    @19
    cF
    cG
    @11
    @12
    @14
    iswlkon
    syl
    mpbir3and
end
