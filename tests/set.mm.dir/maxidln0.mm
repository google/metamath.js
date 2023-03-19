include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "cidl.mm"
include "maxidlidl.mm"
include "idl0cl.mm"
include "syldan.mm"
include "maxidln1.mm"
include "nelneq.mm"
include "syl2anc.mm"
include "neqned.mm"
include "necomd.mm"

theorem maxidln0
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  assume maxidln0.1: |- G = ( 1st ` R )
  assume maxidln0.2: |- H = ( 2nd ` R )
  assume maxidln0.3: |- Z = ( GId ` G )
  assume maxidln0.4: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> U =/= Z )

  proof
    cR
    crngo
    wcel
    #
    cM
    cR
    cmaxidl
    cfv
    wcel
    #
    wa
    #
    cZ
    cU
    @2
    cZ
    cU
    @2
    cZ
    cM
    wcel
    #
    cU
    cM
    wcel
    wn
    cZ
    cU
    wceq
    wn
    @0
    @1
    cM
    cR
    cidl
    cfv
    wcel
    @3
    cR
    cM
    maxidlidl
    cR
    cG
    cM
    cZ
    maxidln0.1
    maxidln0.3
    idl0cl
    syldan
    cR
    cU
    cH
    cM
    maxidln0.2
    maxidln0.4
    maxidln1
    cZ
    cU
    cM
    nelneq
    syl2anc
    neqned
    necomd
end
