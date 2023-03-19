include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cpjh.mm"
include "cva.mm"
include "wceq.mm"
include "wi.mm"
include "cif.mm"
include "c0v.mm"
include "sseq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "sseq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "imbi2d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjcji.mm"
include "dedth3h.mm"

theorem pjcjt2
  let cA: class A
  let cG: class G
  let cH: class H


  assert |- ( ( H e. CH /\ G e. CH /\ A e. ~H ) -> ( H C_ ( _|_ ` G ) -> ( ( projh ` ( H vH G ) ) ` A ) = ( ( ( projh ` H ) ` A ) +h ( ( projh ` G ) ` A ) ) ) )

  proof
    cH
    cch
    wcel
    #
    cG
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cH
    cG
    cort
    cfv
    #
    wss
    #
    cA
    cH
    cG
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    cG
    cpjh
    cfv
    #
    cfv
    #
    cva
    co
    #
    wceq
    #
    wi
    @0
    cH
    chil
    cif
    #
    @3
    wss
    #
    cA
    @14
    cG
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    @14
    cpjh
    cfv
    #
    cfv
    #
    @11
    cva
    co
    #
    wceq
    #
    wi
    @14
    @1
    cG
    chil
    cif
    #
    cort
    cfv
    #
    wss
    #
    cA
    @14
    @23
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    @20
    cA
    @23
    cpjh
    cfv
    #
    cfv
    #
    cva
    co
    #
    wceq
    #
    wi
    @25
    @2
    cA
    c0v
    cif
    #
    @27
    cfv
    #
    @33
    @19
    cfv
    #
    @33
    @29
    cfv
    #
    cva
    co
    #
    wceq
    #
    wi
    cH
    cG
    cA
    chil
    chil
    c0v
    cH
    @14
    wceq
    #
    @4
    @15
    @13
    @22
    cH
    @14
    @3
    sseq1
    @39
    @7
    @18
    @12
    @21
    @39
    cA
    @6
    @17
    @39
    @5
    @16
    cpjh
    cH
    @14
    cG
    chj
    oveq1
    fveq2d
    fveq1d
    @39
    @9
    @20
    @11
    cva
    @39
    cA
    @8
    @19
    cH
    @14
    cpjh
    fveq2
    fveq1d
    oveq1d
    eqeq12d
    imbi12d
    cG
    @23
    wceq
    #
    @15
    @25
    @22
    @32
    @40
    @3
    @24
    @14
    cG
    @23
    cort
    fveq2
    sseq2d
    @40
    @18
    @28
    @21
    @31
    @40
    cA
    @17
    @27
    @40
    @16
    @26
    cpjh
    cG
    @23
    @14
    chj
    oveq2
    fveq2d
    fveq1d
    @40
    @11
    @30
    @20
    cva
    @40
    cA
    @10
    @29
    cG
    @23
    cpjh
    fveq2
    fveq1d
    oveq2d
    eqeq12d
    imbi12d
    cA
    @33
    wceq
    #
    @32
    @38
    @25
    @41
    @28
    @34
    @31
    @37
    cA
    @33
    @27
    fveq2
    @41
    @20
    @35
    @30
    @36
    cva
    cA
    @33
    @19
    fveq2
    cA
    @33
    @29
    fveq2
    oveq12d
    eqeq12d
    imbi2d
    @33
    @23
    @14
    cH
    ifchhv
    cA
    ifhvhv0
    cG
    ifchhv
    pjcji
    dedth3h
end
