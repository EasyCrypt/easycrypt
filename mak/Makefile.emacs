PG_DIR=$(TOOLDIR)/proofgeneral
PG_SRC_DIR=$(PG_DIR)/certicrypt

GEN_KEYWORDS_SH=$(PG_DIR)/certicrypt/gen-pg-keywords.sh

dist_proofgeneral:
	@mkdir -p $(DIST_DIR)
	@cp -R proofgeneral $(DIST_DIR)/proofgeneral

gen_keywords: $(SRC_DIR)/ecLexer.mll
	$(GEN_KEYWORDS_SH) $(SRC_DIR)/ecLexer.mll $(PG_DIR)/certicrypt/certicrypt-keywords.el

install_proofgeneral: gen_keywords
	-mkdir -p $(PROOF_GENERAL_PATH)/certicrypt/
	cp -f proofgeneral/certicrypt/* $(PROOF_GENERAL_PATH)/certicrypt/

install_message:
	@echo "****************************************************************"
	@echo ""
	@echo ";;You need to load Proof General in you ~/.emacs like this "
	@echo ""
	@echo "(load-file \"$(PROOF_GENERAL_PATH)/generic/proof-site.el\")"
	@echo ""
	@echo ";;Set the path to the EasyCrypt executable and the prelude file in your"
	@echo ""
	@echo "(custom-set-variables"
	@echo "..."
	@echo "'(certicrypt-prog-name"
	@echo "  \"$(BINDIR)/easycrypt -emacs -prelude $(includedir_aux)/easycrypt_base.ec\")"
	@echo "..."
	@echo ")"
	@echo ""
	@echo "****************************************************************"
	@echo "And add in $(PROOF_GENERAL_PATH)/generic/proof-site.el"
	@echo ""
	@echo "(defconst proof-assistant-table-default"
	@echo "..."
	@echo "(certicrypt  \"CertiCrypt\"  \"ec\")"
	@echo "..."
	@echo ""


uninstall_proofgeneral:
	rm -Rf $(PROOF_GENERAL_PATH)/certicrypt
